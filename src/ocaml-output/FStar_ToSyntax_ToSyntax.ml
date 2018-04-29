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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
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
  fun uu___88_1708  ->
    match uu___88_1708 with
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
      fun uu___89_1754  ->
        match uu___89_1754 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1782 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1782, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1791 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1791 with
             | (env1,a1) ->
                 (((let uu___113_1817 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___113_1817.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___113_1817.FStar_Syntax_Syntax.index);
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
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
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
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
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
                  FStar_Syntax_Syntax.Delta_constant
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
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___90_2173  ->
    match uu___90_2173 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2174 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2186 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2186)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2205 =
      let uu____2206 = unparen t  in uu____2206.FStar_Parser_AST.tm  in
    match uu____2205 with
    | FStar_Parser_AST.Wild  ->
        let uu____2211 =
          let uu____2212 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2212  in
        FStar_Util.Inr uu____2211
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2223)) ->
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
             let uu____2288 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2288
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2299 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2299
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2310 =
               let uu____2315 =
                 let uu____2316 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2316
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2315)
                in
             FStar_Errors.raise_error uu____2310 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2321 ->
        let rec aux t1 univargs =
          let uu____2355 =
            let uu____2356 = unparen t1  in uu____2356.FStar_Parser_AST.tm
             in
          match uu____2355 with
          | FStar_Parser_AST.App (t2,targ,uu____2363) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___91_2386  ->
                     match uu___91_2386 with
                     | FStar_Util.Inr uu____2391 -> true
                     | uu____2392 -> false) univargs
              then
                let uu____2397 =
                  let uu____2398 =
                    FStar_List.map
                      (fun uu___92_2407  ->
                         match uu___92_2407 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2398  in
                FStar_Util.Inr uu____2397
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___93_2424  ->
                        match uu___93_2424 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2430 -> failwith "impossible")
                     univargs
                    in
                 let uu____2431 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2431)
          | uu____2437 ->
              let uu____2438 =
                let uu____2443 =
                  let uu____2444 =
                    let uu____2445 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2445 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2444  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2443)  in
              FStar_Errors.raise_error uu____2438 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2454 ->
        let uu____2455 =
          let uu____2460 =
            let uu____2461 =
              let uu____2462 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2462 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2461  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2460)  in
        FStar_Errors.raise_error uu____2455 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____2495 ->
        let uu____2518 =
          let uu____2523 =
            let uu____2524 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____2524
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____2523)  in
        FStar_Errors.raise_error uu____2518 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____2534 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2534) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2562 = FStar_List.hd fields  in
        match uu____2562 with
        | (f,uu____2572) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2584 =
                match uu____2584 with
                | (f',uu____2590) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2592 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____2592
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
              (let uu____2596 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2596);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2955 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2962 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2963 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2965,pats1) ->
                let aux out uu____3003 =
                  match uu____3003 with
                  | (p2,uu____3015) ->
                      let intersection =
                        let uu____3023 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3023 out  in
                      let uu____3026 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3026
                      then
                        let uu____3029 = pat_vars p2  in
                        FStar_Util.set_union out uu____3029
                      else
                        (let duplicate_bv =
                           let uu____3034 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3034  in
                         let uu____3037 =
                           let uu____3042 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3042)
                            in
                         FStar_Errors.raise_error uu____3037 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3062 = pat_vars p1  in
              FStar_All.pipe_right uu____3062 (fun a238  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3090 =
                  let uu____3091 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3091  in
                if uu____3090
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3098 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3098  in
                   let first_nonlinear_var =
                     let uu____3102 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3102  in
                   let uu____3105 =
                     let uu____3110 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3110)  in
                   FStar_Errors.raise_error uu____3105 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3114) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3115) -> ()
         | (true ,uu____3122) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3145 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____3145 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3161 ->
               let uu____3164 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____3164 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3276 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____3292 =
                 let uu____3293 =
                   let uu____3294 =
                     let uu____3301 =
                       let uu____3302 =
                         let uu____3307 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____3307, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____3302  in
                     (uu____3301, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____3294  in
                 {
                   FStar_Parser_AST.pat = uu____3293;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____3292
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____3324 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____3325 = aux loc env1 p2  in
                 match uu____3325 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___114_3383 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___115_3388 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___115_3388.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___115_3388.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___114_3383.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___116_3390 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___117_3395 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___117_3395.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___117_3395.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___116_3390.FStar_Syntax_Syntax.p)
                           }
                       | uu____3396 when top -> p4
                       | uu____3397 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____3400 =
                       match binder with
                       | LetBinder uu____3413 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____3433 = close_fun env1 t  in
                             desugar_term env1 uu____3433  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____3435 -> true)
                            then
                              (let uu____3436 =
                                 let uu____3441 =
                                   let uu____3442 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____3443 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____3444 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3442 uu____3443 uu____3444
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3441)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3436)
                            else ();
                            (let uu____3446 = annot_pat_var p3 t1  in
                             (uu____3446,
                               (LocalBinder
                                  ((let uu___118_3452 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___118_3452.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___118_3452.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____3400 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3474 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3474, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3483 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3483, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3502 = resolvex loc env1 x  in
               (match uu____3502 with
                | (loc1,env2,xbv) ->
                    let uu____3524 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3524, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3543 = resolvex loc env1 x  in
               (match uu____3543 with
                | (loc1,env2,xbv) ->
                    let uu____3565 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3565, imp))
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
               let uu____3575 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3575, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3597;_},args)
               ->
               let uu____3603 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3644  ->
                        match uu____3644 with
                        | (loc1,env2,args1) ->
                            let uu____3692 = aux loc1 env2 arg  in
                            (match uu____3692 with
                             | (loc2,env3,uu____3721,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____3603 with
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
                    let uu____3791 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3791, false))
           | FStar_Parser_AST.PatApp uu____3806 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3828 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3861  ->
                        match uu____3861 with
                        | (loc1,env2,pats1) ->
                            let uu____3893 = aux loc1 env2 pat  in
                            (match uu____3893 with
                             | (loc2,env3,uu____3918,pat1,uu____3920) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3828 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3963 =
                        let uu____3966 =
                          let uu____3973 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3973  in
                        let uu____3974 =
                          let uu____3975 =
                            let uu____3988 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3988, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3975  in
                        FStar_All.pipe_left uu____3966 uu____3974  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____4020 =
                               let uu____4021 =
                                 let uu____4034 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____4034, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____4021  in
                             FStar_All.pipe_left (pos_r r) uu____4020) pats1
                        uu____3963
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
               let uu____4076 =
                 FStar_List.fold_left
                   (fun uu____4116  ->
                      fun p2  ->
                        match uu____4116 with
                        | (loc1,env2,pats) ->
                            let uu____4165 = aux loc1 env2 p2  in
                            (match uu____4165 with
                             | (loc2,env3,uu____4194,pat,uu____4196) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4076 with
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
                    let uu____4291 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____4291 with
                     | (constr,uu____4313) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____4316 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____4318 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____4318, false)))
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
                      (fun uu____4387  ->
                         match uu____4387 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4417  ->
                         match uu____4417 with
                         | (f,uu____4423) ->
                             let uu____4424 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4450  ->
                                       match uu____4450 with
                                       | (g,uu____4456) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____4424 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4461,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____4468 =
                   let uu____4469 =
                     let uu____4476 =
                       let uu____4477 =
                         let uu____4478 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____4478  in
                       FStar_Parser_AST.mk_pattern uu____4477
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____4476, args)  in
                   FStar_Parser_AST.PatApp uu____4469  in
                 FStar_Parser_AST.mk_pattern uu____4468
                   p1.FStar_Parser_AST.prange
                  in
               let uu____4481 = aux loc env1 app  in
               (match uu____4481 with
                | (env2,e,b,p2,uu____4510) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4538 =
                            let uu____4539 =
                              let uu____4552 =
                                let uu___119_4553 = fv  in
                                let uu____4554 =
                                  let uu____4557 =
                                    let uu____4558 =
                                      let uu____4565 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4565)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4558
                                     in
                                  FStar_Pervasives_Native.Some uu____4557  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___119_4553.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___119_4553.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4554
                                }  in
                              (uu____4552, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____4539  in
                          FStar_All.pipe_left pos uu____4538
                      | uu____4592 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4646 = aux' true loc env1 p2  in
               (match uu____4646 with
                | (loc1,env2,var,p3,uu____4673) ->
                    let uu____4678 =
                      FStar_List.fold_left
                        (fun uu____4710  ->
                           fun p4  ->
                             match uu____4710 with
                             | (loc2,env3,ps1) ->
                                 let uu____4743 = aux' true loc2 env3 p4  in
                                 (match uu____4743 with
                                  | (loc3,env4,uu____4768,p5,uu____4770) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____4678 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4821 ->
               let uu____4822 = aux' true loc env1 p1  in
               (match uu____4822 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4862 = aux_maybe_or env p  in
         match uu____4862 with
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
            let uu____4921 =
              let uu____4922 =
                let uu____4933 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4933,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4922  in
            (env, uu____4921, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4961 =
                  let uu____4962 =
                    let uu____4967 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4967, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4962  in
                mklet uu____4961
            | FStar_Parser_AST.PatVar (x,uu____4969) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4975);
                   FStar_Parser_AST.prange = uu____4976;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4996 =
                  let uu____4997 =
                    let uu____5008 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____5009 =
                      let uu____5016 = desugar_term env t  in
                      (uu____5016, tacopt1)  in
                    (uu____5008, uu____5009)  in
                  LetBinder uu____4997  in
                (env, uu____4996, [])
            | uu____5027 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5037 = desugar_data_pat env p is_mut  in
             match uu____5037 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5066;
                       FStar_Syntax_Syntax.p = uu____5067;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5068;
                       FStar_Syntax_Syntax.p = uu____5069;_}::[] -> []
                   | uu____5070 -> p1  in
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
  fun uu____5077  ->
    fun env  ->
      fun pat  ->
        let uu____5080 = desugar_data_pat env pat false  in
        match uu____5080 with | (env1,uu____5096,pat1) -> (env1, pat1)

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
      let uu____5115 = desugar_term_aq env e  in
      match uu____5115 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____5132 = desugar_typ_aq env e  in
      match uu____5132 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5142  ->
        fun range  ->
          match uu____5142 with
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
              ((let uu____5152 =
                  let uu____5153 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5153  in
                if uu____5152
                then
                  let uu____5154 =
                    let uu____5159 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5159)  in
                  FStar_Errors.log_issue range uu____5154
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
                  let uu____5164 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____5164 range  in
                let lid1 =
                  let uu____5168 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____5168 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____5178) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5187 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____5187 range  in
                           let private_fv =
                             let uu____5189 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5189 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___120_5190 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___120_5190.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___120_5190.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5191 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5198 =
                        let uu____5203 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5203)
                         in
                      FStar_Errors.raise_error uu____5198 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____5219 =
                  let uu____5226 =
                    let uu____5227 =
                      let uu____5242 =
                        let uu____5251 =
                          let uu____5258 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____5258)  in
                        [uu____5251]  in
                      (lid1, uu____5242)  in
                    FStar_Syntax_Syntax.Tm_app uu____5227  in
                  FStar_Syntax_Syntax.mk uu____5226  in
                uu____5219 FStar_Pervasives_Native.None range))

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
            let uu____5297 =
              let uu____5306 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____5306 l  in
            match uu____5297 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____5361;
                              FStar_Syntax_Syntax.vars = uu____5362;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5385 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5385 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5393 =
                                 let uu____5394 =
                                   let uu____5397 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____5397  in
                                 uu____5394.FStar_Syntax_Syntax.n  in
                               match uu____5393 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____5413))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5414 -> msg
                             else msg  in
                           let uu____5416 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5416
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5419 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5419 " is deprecated"  in
                           let uu____5420 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5420
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5421 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____5426 =
                      let uu____5427 =
                        let uu____5434 = mk_ref_read tm1  in
                        (uu____5434,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____5427  in
                    FStar_All.pipe_left mk1 uu____5426
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____5452 =
          let uu____5453 = unparen t  in uu____5453.FStar_Parser_AST.tm  in
        match uu____5452 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5454; FStar_Ident.ident = uu____5455;
              FStar_Ident.nsstr = uu____5456; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5459 ->
            let uu____5460 =
              let uu____5465 =
                let uu____5466 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5466  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5465)  in
            FStar_Errors.raise_error uu____5460 t.FStar_Parser_AST.range
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
          let uu___121_5561 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___121_5561.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___121_5561.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5564 =
          let uu____5565 = unparen top  in uu____5565.FStar_Parser_AST.tm  in
        match uu____5564 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5570 ->
            let uu____5577 = desugar_formula env top  in (uu____5577, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____5584 = desugar_formula env t  in (uu____5584, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____5591 = desugar_formula env t  in (uu____5591, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____5615 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____5615, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5617 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____5617, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____5625 =
                let uu____5626 =
                  let uu____5633 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____5633, args)  in
                FStar_Parser_AST.Op uu____5626  in
              FStar_Parser_AST.mk_term uu____5625 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____5636 =
              let uu____5637 =
                let uu____5638 =
                  let uu____5645 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____5645, [e])  in
                FStar_Parser_AST.Op uu____5638  in
              FStar_Parser_AST.mk_term uu____5637 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____5636
        | FStar_Parser_AST.Op (op_star,uu____5649::uu____5650::[]) when
            (let uu____5655 = FStar_Ident.text_of_id op_star  in
             uu____5655 = "*") &&
              (let uu____5657 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5657 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5672;_},t1::t2::[])
                  ->
                  let uu____5677 = flatten1 t1  in
                  FStar_List.append uu____5677 [t2]
              | uu____5680 -> [t]  in
            let uu____5681 =
              let uu____5706 =
                let uu____5729 =
                  let uu____5732 = unparen top  in flatten1 uu____5732  in
                FStar_All.pipe_right uu____5729
                  (FStar_List.map
                     (fun t  ->
                        let uu____5767 = desugar_typ_aq env t  in
                        match uu____5767 with
                        | (t',aq) ->
                            let uu____5778 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5778, aq)))
                 in
              FStar_All.pipe_right uu____5706 FStar_List.unzip  in
            (match uu____5681 with
             | (targs,aqs) ->
                 let uu____5887 =
                   let uu____5892 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5892
                    in
                 (match uu____5887 with
                  | (tup,uu____5908) ->
                      let uu____5909 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5909, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5921 =
              let uu____5922 =
                let uu____5925 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5925  in
              FStar_All.pipe_left setpos uu____5922  in
            (uu____5921, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5937 =
              let uu____5942 =
                let uu____5943 =
                  let uu____5944 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____5944 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____5943  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5942)  in
            FStar_Errors.raise_error uu____5937 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5955 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5955 with
             | FStar_Pervasives_Native.None  ->
                 let uu____5962 =
                   let uu____5967 =
                     let uu____5968 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5968
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5967)
                    in
                 FStar_Errors.raise_error uu____5962
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5978 =
                     let uu____6003 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____6065 = desugar_term_aq env t  in
                               match uu____6065 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____6003 FStar_List.unzip  in
                   (match uu____5978 with
                    | (args1,aqs) ->
                        let uu____6198 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6198, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6212)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6227 =
              let uu___122_6228 = top  in
              let uu____6229 =
                let uu____6230 =
                  let uu____6237 =
                    let uu___123_6238 = top  in
                    let uu____6239 =
                      let uu____6240 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6240  in
                    {
                      FStar_Parser_AST.tm = uu____6239;
                      FStar_Parser_AST.range =
                        (uu___123_6238.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___123_6238.FStar_Parser_AST.level)
                    }  in
                  (uu____6237, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6230  in
              {
                FStar_Parser_AST.tm = uu____6229;
                FStar_Parser_AST.range =
                  (uu___122_6228.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___122_6228.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6227
        | FStar_Parser_AST.Construct (n1,(a,uu____6243)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6259 =
                let uu___124_6260 = top  in
                let uu____6261 =
                  let uu____6262 =
                    let uu____6269 =
                      let uu___125_6270 = top  in
                      let uu____6271 =
                        let uu____6272 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____6272  in
                      {
                        FStar_Parser_AST.tm = uu____6271;
                        FStar_Parser_AST.range =
                          (uu___125_6270.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___125_6270.FStar_Parser_AST.level)
                      }  in
                    (uu____6269, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____6262  in
                {
                  FStar_Parser_AST.tm = uu____6261;
                  FStar_Parser_AST.range =
                    (uu___124_6260.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___124_6260.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____6259))
        | FStar_Parser_AST.Construct (n1,(a,uu____6275)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6290 =
              let uu___126_6291 = top  in
              let uu____6292 =
                let uu____6293 =
                  let uu____6300 =
                    let uu___127_6301 = top  in
                    let uu____6302 =
                      let uu____6303 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6303  in
                    {
                      FStar_Parser_AST.tm = uu____6302;
                      FStar_Parser_AST.range =
                        (uu___127_6301.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___127_6301.FStar_Parser_AST.level)
                    }  in
                  (uu____6300, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6293  in
              {
                FStar_Parser_AST.tm = uu____6292;
                FStar_Parser_AST.range =
                  (uu___126_6291.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___126_6291.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6290
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6304; FStar_Ident.ident = uu____6305;
              FStar_Ident.nsstr = uu____6306; FStar_Ident.str = "Type0";_}
            ->
            let uu____6309 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____6309, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6310; FStar_Ident.ident = uu____6311;
              FStar_Ident.nsstr = uu____6312; FStar_Ident.str = "Type";_}
            ->
            let uu____6315 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____6315, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6316; FStar_Ident.ident = uu____6317;
               FStar_Ident.nsstr = uu____6318; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____6336 =
              let uu____6337 =
                let uu____6338 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____6338  in
              mk1 uu____6337  in
            (uu____6336, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6339; FStar_Ident.ident = uu____6340;
              FStar_Ident.nsstr = uu____6341; FStar_Ident.str = "Effect";_}
            ->
            let uu____6344 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____6344, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6345; FStar_Ident.ident = uu____6346;
              FStar_Ident.nsstr = uu____6347; FStar_Ident.str = "True";_}
            ->
            let uu____6350 =
              let uu____6351 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6351
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6350, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6352; FStar_Ident.ident = uu____6353;
              FStar_Ident.nsstr = uu____6354; FStar_Ident.str = "False";_}
            ->
            let uu____6357 =
              let uu____6358 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6358
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6357, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____6361;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____6363 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____6363 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____6372 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_defined_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____6372, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____6373 =
                    let uu____6374 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____6374 txt
                     in
                  failwith uu____6373))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6381 = desugar_name mk1 setpos env true l  in
              (uu____6381, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6384 = desugar_name mk1 setpos env true l  in
              (uu____6384, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____6395 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____6395 with
                | FStar_Pervasives_Native.Some uu____6404 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____6409 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____6409 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6423 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____6440 =
                    let uu____6441 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____6441  in
                  (uu____6440, noaqs)
              | uu____6442 ->
                  let uu____6449 =
                    let uu____6454 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6454)  in
                  FStar_Errors.raise_error uu____6449
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6461 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____6461 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6468 =
                    let uu____6473 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6473)
                     in
                  FStar_Errors.raise_error uu____6468
                    top.FStar_Parser_AST.range
              | uu____6478 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____6482 = desugar_name mk1 setpos env true lid'  in
                  (uu____6482, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6498 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6498 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6517 ->
                       let uu____6524 =
                         FStar_Util.take
                           (fun uu____6548  ->
                              match uu____6548 with
                              | (uu____6553,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____6524 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____6598 =
                              let uu____6623 =
                                FStar_List.map
                                  (fun uu____6666  ->
                                     match uu____6666 with
                                     | (t,imp) ->
                                         let uu____6683 =
                                           desugar_term_aq env t  in
                                         (match uu____6683 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____6623
                                FStar_List.unzip
                               in
                            (match uu____6598 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____6824 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____6824, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____6840 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____6840 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6847 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6858 =
              FStar_List.fold_left
                (fun uu____6899  ->
                   fun b  ->
                     match uu____6899 with
                     | (env1,tparams,typs) ->
                         let uu____6948 = desugar_binder env1 b  in
                         (match uu____6948 with
                          | (xopt,t1) ->
                              let uu____6975 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6984 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6984)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6975 with
                               | (env2,x) ->
                                   let uu____7002 =
                                     let uu____7005 =
                                       let uu____7008 =
                                         let uu____7009 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7009
                                          in
                                       [uu____7008]  in
                                     FStar_List.append typs uu____7005  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___128_7033 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___128_7033.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___128_7033.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____7002)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6858 with
             | (env1,uu____7057,targs) ->
                 let uu____7075 =
                   let uu____7080 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7080
                    in
                 (match uu____7075 with
                  | (tup,uu____7090) ->
                      let uu____7091 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7091, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7108 = uncurry binders t  in
            (match uu____7108 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___94_7152 =
                   match uu___94_7152 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7168 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7168
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7190 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7190 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7223 = aux env [] bs  in (uu____7223, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7232 = desugar_binder env b  in
            (match uu____7232 with
             | (FStar_Pervasives_Native.None ,uu____7243) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7257 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____7257 with
                  | ((x,uu____7273),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____7286 =
                        let uu____7287 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____7287  in
                      (uu____7286, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____7305 =
              FStar_List.fold_left
                (fun uu____7325  ->
                   fun pat  ->
                     match uu____7325 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____7351,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____7361 =
                                let uu____7364 = free_type_vars env1 t  in
                                FStar_List.append uu____7364 ftvs  in
                              (env1, uu____7361)
                          | FStar_Parser_AST.PatAscribed
                              (uu____7369,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____7380 =
                                let uu____7383 = free_type_vars env1 t  in
                                let uu____7386 =
                                  let uu____7389 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____7389 ftvs  in
                                FStar_List.append uu____7383 uu____7386  in
                              (env1, uu____7380)
                          | uu____7394 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____7305 with
             | (uu____7403,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____7415 =
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
                   FStar_List.append uu____7415 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___95_7470 =
                   match uu___95_7470 with
                   | [] ->
                       let uu____7495 = desugar_term_aq env1 body  in
                       (match uu____7495 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7532 =
                                      let uu____7533 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7533
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7532 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7602 =
                              let uu____7605 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7605  in
                            (uu____7602, aq))
                   | p::rest ->
                       let uu____7618 = desugar_binding_pat env1 p  in
                       (match uu____7618 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7652 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7659 =
                              match b with
                              | LetBinder uu____7696 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7762) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7816 =
                                          let uu____7823 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7823, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7816
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7879,uu____7880) ->
                                             let tup2 =
                                               let uu____7882 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7882
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7886 =
                                                 let uu____7893 =
                                                   let uu____7894 =
                                                     let uu____7909 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7912 =
                                                       let uu____7921 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7928 =
                                                         let uu____7937 =
                                                           let uu____7944 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7944
                                                            in
                                                         [uu____7937]  in
                                                       uu____7921 ::
                                                         uu____7928
                                                        in
                                                     (uu____7909, uu____7912)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7894
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7893
                                                  in
                                               uu____7886
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____7985 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7985
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____8028,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____8030,pats)) ->
                                             let tupn =
                                               let uu____8069 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8069
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8079 =
                                                 let uu____8080 =
                                                   let uu____8095 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____8098 =
                                                     let uu____8107 =
                                                       let uu____8116 =
                                                         let uu____8123 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____8123
                                                          in
                                                       [uu____8116]  in
                                                     FStar_List.append args
                                                       uu____8107
                                                      in
                                                   (uu____8095, uu____8098)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8080
                                                  in
                                               mk1 uu____8079  in
                                             let p2 =
                                               let uu____8161 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____8161
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____8202 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7659 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____8283,uu____8284,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____8306 =
                let uu____8307 = unparen e  in uu____8307.FStar_Parser_AST.tm
                 in
              match uu____8306 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____8317 ->
                  let uu____8318 = desugar_term_aq env e  in
                  (match uu____8318 with
                   | (head1,aq) ->
                       let uu____8331 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____8331, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____8338 ->
            let rec aux args aqs e =
              let uu____8417 =
                let uu____8418 = unparen e  in uu____8418.FStar_Parser_AST.tm
                 in
              match uu____8417 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____8438 = desugar_term_aq env t  in
                  (match uu____8438 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____8474 ->
                  let uu____8475 = desugar_term_aq env e  in
                  (match uu____8475 with
                   | (head1,aq) ->
                       let uu____8498 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____8498, (join_aqs (aq :: aqs))))
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
            let uu____8560 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____8560
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
            let uu____8612 = desugar_term_aq env t  in
            (match uu____8612 with
             | (tm,s) ->
                 let uu____8623 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____8623, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____8629 =
              let uu____8642 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____8642 then desugar_typ_aq else desugar_term_aq  in
            uu____8629 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8697 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8840  ->
                        match uu____8840 with
                        | (attr_opt,(p,def)) ->
                            let uu____8898 = is_app_pattern p  in
                            if uu____8898
                            then
                              let uu____8929 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8929, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____9011 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____9011, def1)
                               | uu____9056 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____9094);
                                           FStar_Parser_AST.prange =
                                             uu____9095;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____9143 =
                                            let uu____9164 =
                                              let uu____9169 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9169  in
                                            (uu____9164, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____9143, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____9260) ->
                                        if top_level
                                        then
                                          let uu____9295 =
                                            let uu____9316 =
                                              let uu____9321 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9321  in
                                            (uu____9316, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____9295, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____9411 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____9442 =
                FStar_List.fold_left
                  (fun uu____9515  ->
                     fun uu____9516  ->
                       match (uu____9515, uu____9516) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____9624,uu____9625),uu____9626))
                           ->
                           let uu____9743 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9769 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9769 with
                                  | (env2,xx) ->
                                      let uu____9788 =
                                        let uu____9791 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9791 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9788))
                             | FStar_Util.Inr l ->
                                 let uu____9799 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____9799, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9743 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____9442 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9947 =
                    match uu____9947 with
                    | (attrs_opt,(uu____9983,args,result_t),def) ->
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
                                let uu____10071 = is_comp_type env1 t  in
                                if uu____10071
                                then
                                  ((let uu____10073 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____10083 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____10083))
                                       in
                                    match uu____10073 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____10086 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____10088 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____10088))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____10086
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____10092 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____10092 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____10096 ->
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
                              let uu____10111 =
                                let uu____10112 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____10112
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____10111
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
                  let uu____10187 = desugar_term_aq env' body  in
                  (match uu____10187 with
                   | (body1,aq) ->
                       let uu____10200 =
                         let uu____10203 =
                           let uu____10204 =
                             let uu____10217 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____10217)  in
                           FStar_Syntax_Syntax.Tm_let uu____10204  in
                         FStar_All.pipe_left mk1 uu____10203  in
                       (uu____10200, aq))
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
              let uu____10295 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____10295 with
              | (env1,binder,pat1) ->
                  let uu____10317 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____10343 = desugar_term_aq env1 t2  in
                        (match uu____10343 with
                         | (body1,aq) ->
                             let fv =
                               let uu____10357 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____10357
                                 FStar_Pervasives_Native.None
                                in
                             let uu____10358 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____10358, aq))
                    | LocalBinder (x,uu____10388) ->
                        let uu____10389 = desugar_term_aq env1 t2  in
                        (match uu____10389 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____10403;
                                   FStar_Syntax_Syntax.p = uu____10404;_}::[]
                                   -> body1
                               | uu____10405 ->
                                   let uu____10408 =
                                     let uu____10415 =
                                       let uu____10416 =
                                         let uu____10439 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____10442 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____10439, uu____10442)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____10416
                                        in
                                     FStar_Syntax_Syntax.mk uu____10415  in
                                   uu____10408 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____10482 =
                               let uu____10485 =
                                 let uu____10486 =
                                   let uu____10499 =
                                     let uu____10502 =
                                       let uu____10503 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____10503]  in
                                     FStar_Syntax_Subst.close uu____10502
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____10499)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____10486  in
                               FStar_All.pipe_left mk1 uu____10485  in
                             (uu____10482, aq))
                     in
                  (match uu____10317 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____10560 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____10560, aq)
                       else (tm, aq))
               in
            let uu____10572 = FStar_List.hd lbs  in
            (match uu____10572 with
             | (attrs,(head_pat,defn)) ->
                 let uu____10616 = is_rec || (is_app_pattern head_pat)  in
                 if uu____10616
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____10629 =
                let uu____10630 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____10630  in
              mk1 uu____10629  in
            let uu____10631 = desugar_term_aq env t1  in
            (match uu____10631 with
             | (t1',aq1) ->
                 let uu____10642 = desugar_term_aq env t2  in
                 (match uu____10642 with
                  | (t2',aq2) ->
                      let uu____10653 = desugar_term_aq env t3  in
                      (match uu____10653 with
                       | (t3',aq3) ->
                           let uu____10664 =
                             let uu____10665 =
                               let uu____10666 =
                                 let uu____10689 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None)
                                    in
                                 let uu____10710 =
                                   let uu____10727 =
                                     let uu____10742 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____10742,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____10755 =
                                     let uu____10772 =
                                       let uu____10787 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____10787,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____10772]  in
                                   uu____10727 :: uu____10755  in
                                 (uu____10689, uu____10710)  in
                               FStar_Syntax_Syntax.Tm_match uu____10666  in
                             mk1 uu____10665  in
                           (uu____10664, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10986 =
              match uu____10986 with
              | (pat,wopt,b) ->
                  let uu____11008 = desugar_match_pat env pat  in
                  (match uu____11008 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____11039 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____11039
                          in
                       let uu____11040 = desugar_term_aq env1 b  in
                       (match uu____11040 with
                        | (b1,aq) ->
                            let uu____11053 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____11053, aq)))
               in
            let uu____11058 = desugar_term_aq env e  in
            (match uu____11058 with
             | (e1,aq) ->
                 let uu____11069 =
                   let uu____11102 =
                     let uu____11137 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____11137 FStar_List.unzip  in
                   FStar_All.pipe_right uu____11102
                     (fun uu____11273  ->
                        match uu____11273 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____11069 with
                  | (brs,aqs) ->
                      let uu____11506 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____11506, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____11551 = is_comp_type env t  in
              if uu____11551
              then
                let uu____11560 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____11560
              else
                (let uu____11568 = desugar_term env t  in
                 FStar_Util.Inl uu____11568)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____11578 = desugar_term_aq env e  in
            (match uu____11578 with
             | (e1,aq) ->
                 let uu____11589 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____11589, aq))
        | FStar_Parser_AST.Record (uu____11622,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____11663 = FStar_List.hd fields  in
              match uu____11663 with | (f,uu____11675) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____11721  ->
                        match uu____11721 with
                        | (g,uu____11727) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____11733,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____11747 =
                         let uu____11752 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____11752)
                          in
                       FStar_Errors.raise_error uu____11747
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
                  let uu____11760 =
                    let uu____11771 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____11802  ->
                              match uu____11802 with
                              | (f,uu____11812) ->
                                  let uu____11813 =
                                    let uu____11814 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____11814
                                     in
                                  (uu____11813, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____11771)  in
                  FStar_Parser_AST.Construct uu____11760
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____11832 =
                      let uu____11833 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____11833  in
                    FStar_Parser_AST.mk_term uu____11832
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____11835 =
                      let uu____11848 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____11878  ->
                                match uu____11878 with
                                | (f,uu____11888) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____11848)  in
                    FStar_Parser_AST.Record uu____11835  in
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
            let uu____11948 = desugar_term_aq env recterm1  in
            (match uu____11948 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____11964;
                         FStar_Syntax_Syntax.vars = uu____11965;_},args)
                      ->
                      let uu____11987 =
                        let uu____11988 =
                          let uu____11989 =
                            let uu____12004 =
                              let uu____12007 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____12008 =
                                let uu____12011 =
                                  let uu____12012 =
                                    let uu____12019 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____12019)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____12012
                                   in
                                FStar_Pervasives_Native.Some uu____12011  in
                              FStar_Syntax_Syntax.fvar uu____12007
                                FStar_Syntax_Syntax.Delta_constant
                                uu____12008
                               in
                            (uu____12004, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____11989  in
                        FStar_All.pipe_left mk1 uu____11988  in
                      (uu____11987, s)
                  | uu____12046 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____12050 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____12050 with
              | (constrname,is_rec) ->
                  let uu____12065 = desugar_term_aq env e  in
                  (match uu____12065 with
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
                       let uu____12083 =
                         let uu____12084 =
                           let uu____12085 =
                             let uu____12100 =
                               let uu____12103 =
                                 let uu____12104 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____12104
                                  in
                               FStar_Syntax_Syntax.fvar uu____12103
                                 FStar_Syntax_Syntax.Delta_equational qual
                                in
                             let uu____12105 =
                               let uu____12114 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____12114]  in
                             (uu____12100, uu____12105)  in
                           FStar_Syntax_Syntax.Tm_app uu____12085  in
                         FStar_All.pipe_left mk1 uu____12084  in
                       (uu____12083, s))))
        | FStar_Parser_AST.NamedTyp (uu____12143,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____12152 =
              let uu____12153 = FStar_Syntax_Subst.compress tm  in
              uu____12153.FStar_Syntax_Syntax.n  in
            (match uu____12152 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____12161 =
                   let uu___129_12162 =
                     let uu____12163 =
                       let uu____12164 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____12164  in
                     FStar_Syntax_Util.exp_string uu____12163  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___129_12162.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___129_12162.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____12161, noaqs)
             | uu____12165 ->
                 let uu____12166 =
                   let uu____12171 =
                     let uu____12172 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____12172
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____12171)  in
                 FStar_Errors.raise_error uu____12166
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____12178 = desugar_term_aq env e  in
            (match uu____12178 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____12190 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____12190, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____12196 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____12197 =
              let uu____12198 =
                let uu____12207 = desugar_term env e  in (bv, b, uu____12207)
                 in
              [uu____12198]  in
            (uu____12196, uu____12197)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____12238 =
              let uu____12239 =
                let uu____12240 =
                  let uu____12247 = desugar_term env e  in (uu____12247, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____12240  in
              FStar_All.pipe_left mk1 uu____12239  in
            (uu____12238, noaqs)
        | uu____12252 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____12253 = desugar_formula env top  in
            (uu____12253, noaqs)
        | uu____12254 ->
            let uu____12255 =
              let uu____12260 =
                let uu____12261 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____12261  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____12260)  in
            FStar_Errors.raise_error uu____12255 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____12267 -> false
    | uu____12276 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____12282 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____12282 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____12286 -> false

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
           (fun uu____12323  ->
              match uu____12323 with
              | (a,imp) ->
                  let uu____12336 = desugar_term env a  in
                  arg_withimp_e imp uu____12336))

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
        let is_requires uu____12368 =
          match uu____12368 with
          | (t1,uu____12374) ->
              let uu____12375 =
                let uu____12376 = unparen t1  in
                uu____12376.FStar_Parser_AST.tm  in
              (match uu____12375 with
               | FStar_Parser_AST.Requires uu____12377 -> true
               | uu____12384 -> false)
           in
        let is_ensures uu____12394 =
          match uu____12394 with
          | (t1,uu____12400) ->
              let uu____12401 =
                let uu____12402 = unparen t1  in
                uu____12402.FStar_Parser_AST.tm  in
              (match uu____12401 with
               | FStar_Parser_AST.Ensures uu____12403 -> true
               | uu____12410 -> false)
           in
        let is_app head1 uu____12425 =
          match uu____12425 with
          | (t1,uu____12431) ->
              let uu____12432 =
                let uu____12433 = unparen t1  in
                uu____12433.FStar_Parser_AST.tm  in
              (match uu____12432 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____12435;
                      FStar_Parser_AST.level = uu____12436;_},uu____12437,uu____12438)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____12439 -> false)
           in
        let is_smt_pat uu____12449 =
          match uu____12449 with
          | (t1,uu____12455) ->
              let uu____12456 =
                let uu____12457 = unparen t1  in
                uu____12457.FStar_Parser_AST.tm  in
              (match uu____12456 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____12460);
                             FStar_Parser_AST.range = uu____12461;
                             FStar_Parser_AST.level = uu____12462;_},uu____12463)::uu____12464::[])
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
                             FStar_Parser_AST.range = uu____12503;
                             FStar_Parser_AST.level = uu____12504;_},uu____12505)::uu____12506::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____12531 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____12563 = head_and_args t1  in
          match uu____12563 with
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
                   let thunk_ens uu____12661 =
                     match uu____12661 with
                     | (e,i) ->
                         let uu____12672 = thunk_ens_ e  in (uu____12672, i)
                      in
                   let fail_lemma uu____12684 =
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
                         let uu____12764 =
                           let uu____12771 =
                             let uu____12778 = thunk_ens ens  in
                             [uu____12778; nil_pat]  in
                           req_true :: uu____12771  in
                         unit_tm :: uu____12764
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____12825 =
                           let uu____12832 =
                             let uu____12839 = thunk_ens ens  in
                             [uu____12839; nil_pat]  in
                           req :: uu____12832  in
                         unit_tm :: uu____12825
                     | ens::smtpat::[] when
                         (((let uu____12888 = is_requires ens  in
                            Prims.op_Negation uu____12888) &&
                             (let uu____12890 = is_smt_pat ens  in
                              Prims.op_Negation uu____12890))
                            &&
                            (let uu____12892 = is_decreases ens  in
                             Prims.op_Negation uu____12892))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____12893 =
                           let uu____12900 =
                             let uu____12907 = thunk_ens ens  in
                             [uu____12907; smtpat]  in
                           req_true :: uu____12900  in
                         unit_tm :: uu____12893
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____12954 =
                           let uu____12961 =
                             let uu____12968 = thunk_ens ens  in
                             [uu____12968; nil_pat; dec]  in
                           req_true :: uu____12961  in
                         unit_tm :: uu____12954
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13028 =
                           let uu____13035 =
                             let uu____13042 = thunk_ens ens  in
                             [uu____13042; smtpat; dec]  in
                           req_true :: uu____13035  in
                         unit_tm :: uu____13028
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____13102 =
                           let uu____13109 =
                             let uu____13116 = thunk_ens ens  in
                             [uu____13116; nil_pat; dec]  in
                           req :: uu____13109  in
                         unit_tm :: uu____13102
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13176 =
                           let uu____13183 =
                             let uu____13190 = thunk_ens ens  in
                             [uu____13190; smtpat]  in
                           req :: uu____13183  in
                         unit_tm :: uu____13176
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____13255 =
                           let uu____13262 =
                             let uu____13269 = thunk_ens ens  in
                             [uu____13269; dec; smtpat]  in
                           req :: uu____13262  in
                         unit_tm :: uu____13255
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____13331 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____13331, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13359 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13359
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____13360 =
                     let uu____13367 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13367, [])  in
                   (uu____13360, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13385 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13385
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____13386 =
                     let uu____13393 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13393, [])  in
                   (uu____13386, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____13409 =
                     let uu____13416 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13416, [])  in
                   (uu____13409, [(t1, FStar_Parser_AST.Nothing)])
               | uu____13439 ->
                   let default_effect =
                     let uu____13441 = FStar_Options.ml_ish ()  in
                     if uu____13441
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____13444 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____13444
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____13446 =
                     let uu____13453 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13453, [])  in
                   (uu____13446, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____13476 = pre_process_comp_typ t  in
        match uu____13476 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____13525 =
                  let uu____13530 =
                    let uu____13531 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____13531
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____13530)  in
                fail1 uu____13525)
             else ();
             (let is_universe uu____13542 =
                match uu____13542 with
                | (uu____13547,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____13549 = FStar_Util.take is_universe args  in
              match uu____13549 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____13608  ->
                         match uu____13608 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____13615 =
                    let uu____13630 = FStar_List.hd args1  in
                    let uu____13639 = FStar_List.tl args1  in
                    (uu____13630, uu____13639)  in
                  (match uu____13615 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____13694 =
                         let is_decrease uu____13732 =
                           match uu____13732 with
                           | (t1,uu____13742) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____13752;
                                       FStar_Syntax_Syntax.vars = uu____13753;_},uu____13754::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____13785 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____13694 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____13901  ->
                                      match uu____13901 with
                                      | (t1,uu____13911) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____13920,(arg,uu____13922)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____13951 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____13968 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____13979 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____13979
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____13983 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____13983
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____13990 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____13990
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____13994 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____13994
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____13998 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____13998
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____14002 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____14002
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____14018 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____14018
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
                                                  let uu____14103 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____14103
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
                                            | uu____14118 -> pat  in
                                          let uu____14119 =
                                            let uu____14130 =
                                              let uu____14141 =
                                                let uu____14150 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____14150, aq)  in
                                              [uu____14141]  in
                                            ens :: uu____14130  in
                                          req :: uu____14119
                                      | uu____14191 -> rest2
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
        | uu____14215 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___130_14236 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___130_14236.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___130_14236.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___131_14278 = b  in
             {
               FStar_Parser_AST.b = (uu___131_14278.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___131_14278.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___131_14278.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____14341 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____14341)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____14354 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____14354 with
             | (env1,a1) ->
                 let a2 =
                   let uu___132_14364 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___132_14364.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___132_14364.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____14390 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____14404 =
                     let uu____14407 =
                       let uu____14408 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____14408]  in
                     no_annot_abs uu____14407 body2  in
                   FStar_All.pipe_left setpos uu____14404  in
                 let uu____14423 =
                   let uu____14424 =
                     let uu____14439 =
                       let uu____14442 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____14442
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____14443 =
                       let uu____14452 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____14452]  in
                     (uu____14439, uu____14443)  in
                   FStar_Syntax_Syntax.Tm_app uu____14424  in
                 FStar_All.pipe_left mk1 uu____14423)
        | uu____14483 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____14563 = q (rest, pats, body)  in
              let uu____14570 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____14563 uu____14570
                FStar_Parser_AST.Formula
               in
            let uu____14571 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____14571 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____14580 -> failwith "impossible"  in
      let uu____14583 =
        let uu____14584 = unparen f  in uu____14584.FStar_Parser_AST.tm  in
      match uu____14583 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____14591,uu____14592) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____14603,uu____14604) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____14635 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____14635
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____14671 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____14671
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____14714 -> desugar_term env f

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
      let uu____14719 =
        FStar_List.fold_left
          (fun uu____14755  ->
             fun b  ->
               match uu____14755 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___133_14807 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___133_14807.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___133_14807.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___133_14807.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____14824 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____14824 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___134_14844 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___134_14844.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___134_14844.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____14861 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____14719 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____14948 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14948)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____14953 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14953)
      | FStar_Parser_AST.TVariable x ->
          let uu____14957 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____14957)
      | FStar_Parser_AST.NoName t ->
          let uu____14961 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____14961)
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
               (fun uu___96_15000  ->
                  match uu___96_15000 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____15001 -> false))
           in
        let quals2 q =
          let uu____15014 =
            (let uu____15017 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____15017) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____15014
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____15031 = FStar_Ident.range_of_lid disc_name  in
                let uu____15032 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____15031;
                  FStar_Syntax_Syntax.sigquals = uu____15032;
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
            let uu____15071 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____15105  ->
                        match uu____15105 with
                        | (x,uu____15113) ->
                            let uu____15114 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____15114 with
                             | (field_name,uu____15122) ->
                                 let only_decl =
                                   ((let uu____15126 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____15126)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____15128 =
                                        let uu____15129 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____15129.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____15128)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____15145 =
                                       FStar_List.filter
                                         (fun uu___97_15149  ->
                                            match uu___97_15149 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____15150 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____15145
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___98_15163  ->
                                             match uu___98_15163 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____15164 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____15166 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____15166;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____15171 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____15171
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____15176 =
                                        let uu____15181 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____15181  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____15176;
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
                                      let uu____15185 =
                                        let uu____15186 =
                                          let uu____15193 =
                                            let uu____15196 =
                                              let uu____15197 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____15197
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____15196]  in
                                          ((false, [lb]), uu____15193)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____15186
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____15185;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____15071 FStar_List.flatten
  
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
            (lid,uu____15241,t,uu____15243,n1,uu____15245) when
            let uu____15250 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____15250 ->
            let uu____15251 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____15251 with
             | (formals,uu____15267) ->
                 (match formals with
                  | [] -> []
                  | uu____15290 ->
                      let filter_records uu___99_15304 =
                        match uu___99_15304 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____15307,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____15319 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____15321 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____15321 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____15331 = FStar_Util.first_N n1 formals  in
                      (match uu____15331 with
                       | (uu____15354,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____15380 -> []
  
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
                    let uu____15450 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____15450
                    then
                      let uu____15453 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____15453
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____15456 =
                      let uu____15461 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____15461  in
                    let uu____15462 =
                      let uu____15465 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____15465  in
                    let uu____15468 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____15456;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____15462;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____15468;
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
          let tycon_id uu___100_15519 =
            match uu___100_15519 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____15521,uu____15522) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____15532,uu____15533,uu____15534) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____15544,uu____15545,uu____15546) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____15576,uu____15577,uu____15578) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____15622) ->
                let uu____15623 =
                  let uu____15624 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____15624  in
                FStar_Parser_AST.mk_term uu____15623 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____15626 =
                  let uu____15627 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____15627  in
                FStar_Parser_AST.mk_term uu____15626 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____15629) ->
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
              | uu____15660 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____15666 =
                     let uu____15667 =
                       let uu____15674 = binder_to_term b  in
                       (out, uu____15674, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____15667  in
                   FStar_Parser_AST.mk_term uu____15666
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___101_15686 =
            match uu___101_15686 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____15742  ->
                       match uu____15742 with
                       | (x,t,uu____15753) ->
                           let uu____15758 =
                             let uu____15759 =
                               let uu____15764 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____15764, t)  in
                             FStar_Parser_AST.Annotated uu____15759  in
                           FStar_Parser_AST.mk_binder uu____15758
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____15766 =
                    let uu____15767 =
                      let uu____15768 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____15768  in
                    FStar_Parser_AST.mk_term uu____15767
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____15766 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____15772 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____15799  ->
                          match uu____15799 with
                          | (x,uu____15809,uu____15810) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____15772)
            | uu____15863 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___102_15902 =
            match uu___102_15902 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____15926 = typars_of_binders _env binders  in
                (match uu____15926 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____15968 =
                         let uu____15969 =
                           let uu____15970 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____15970  in
                         FStar_Parser_AST.mk_term uu____15969
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____15968 binders  in
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
            | uu____15981 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____16029 =
              FStar_List.fold_left
                (fun uu____16069  ->
                   fun uu____16070  ->
                     match (uu____16069, uu____16070) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____16161 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____16161 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____16029 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____16274 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____16274
                | uu____16275 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____16283 = desugar_abstract_tc quals env [] tc  in
              (match uu____16283 with
               | (uu____16296,uu____16297,se,uu____16299) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____16302,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____16319 =
                                 let uu____16320 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____16320  in
                               if uu____16319
                               then
                                 let uu____16321 =
                                   let uu____16326 =
                                     let uu____16327 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____16327
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____16326)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____16321
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
                           | uu____16334 ->
                               let uu____16335 =
                                 let uu____16342 =
                                   let uu____16343 =
                                     let uu____16356 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____16356)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____16343
                                    in
                                 FStar_Syntax_Syntax.mk uu____16342  in
                               uu____16335 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___135_16370 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___135_16370.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___135_16370.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___135_16370.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____16371 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____16374 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____16374
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____16387 = typars_of_binders env binders  in
              (match uu____16387 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16423 =
                           FStar_Util.for_some
                             (fun uu___103_16425  ->
                                match uu___103_16425 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____16426 -> false) quals
                            in
                         if uu____16423
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____16433 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___104_16437  ->
                               match uu___104_16437 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____16438 -> false))
                        in
                     if uu____16433
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____16447 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____16447
                     then
                       let uu____16450 =
                         let uu____16457 =
                           let uu____16458 = unparen t  in
                           uu____16458.FStar_Parser_AST.tm  in
                         match uu____16457 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____16479 =
                               match FStar_List.rev args with
                               | (last_arg,uu____16509)::args_rev ->
                                   let uu____16521 =
                                     let uu____16522 = unparen last_arg  in
                                     uu____16522.FStar_Parser_AST.tm  in
                                   (match uu____16521 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____16550 -> ([], args))
                               | uu____16559 -> ([], args)  in
                             (match uu____16479 with
                              | (cattributes,args1) ->
                                  let uu____16598 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____16598))
                         | uu____16609 -> (t, [])  in
                       match uu____16450 with
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
                                  (fun uu___105_16631  ->
                                     match uu___105_16631 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____16632 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____16639)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____16663 = tycon_record_as_variant trec  in
              (match uu____16663 with
               | (t,fs) ->
                   let uu____16680 =
                     let uu____16683 =
                       let uu____16684 =
                         let uu____16693 =
                           let uu____16696 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____16696  in
                         (uu____16693, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____16684  in
                     uu____16683 :: quals  in
                   desugar_tycon env d uu____16680 [t])
          | uu____16701::uu____16702 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____16869 = et  in
                match uu____16869 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____17094 ->
                         let trec = tc  in
                         let uu____17118 = tycon_record_as_variant trec  in
                         (match uu____17118 with
                          | (t,fs) ->
                              let uu____17177 =
                                let uu____17180 =
                                  let uu____17181 =
                                    let uu____17190 =
                                      let uu____17193 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____17193  in
                                    (uu____17190, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____17181
                                   in
                                uu____17180 :: quals1  in
                              collect_tcs uu____17177 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____17280 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17280 with
                          | (env2,uu____17340,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____17489 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17489 with
                          | (env2,uu____17549,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____17674 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____17721 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____17721 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___107_18232  ->
                             match uu___107_18232 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____18299,uu____18300);
                                    FStar_Syntax_Syntax.sigrng = uu____18301;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____18302;
                                    FStar_Syntax_Syntax.sigmeta = uu____18303;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____18304;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____18365 =
                                     typars_of_binders env1 binders  in
                                   match uu____18365 with
                                   | (env2,tpars1) ->
                                       let uu____18396 =
                                         push_tparams env2 tpars1  in
                                       (match uu____18396 with
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
                                 let uu____18429 =
                                   let uu____18450 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____18450)
                                    in
                                 [uu____18429]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____18518);
                                    FStar_Syntax_Syntax.sigrng = uu____18519;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____18521;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____18522;_},constrs,tconstr,quals1)
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
                                 let uu____18620 = push_tparams env1 tpars
                                    in
                                 (match uu____18620 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____18697  ->
                                             match uu____18697 with
                                             | (x,uu____18711) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____18719 =
                                        let uu____18748 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____18862  ->
                                                  match uu____18862 with
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
                                                        let uu____18918 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____18918
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
                                                                uu___106_18929
                                                                 ->
                                                                match uu___106_18929
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____18941
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____18949 =
                                                        let uu____18970 =
                                                          let uu____18971 =
                                                            let uu____18972 =
                                                              let uu____18987
                                                                =
                                                                let uu____18988
                                                                  =
                                                                  let uu____18991
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____18991
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____18988
                                                                 in
                                                              (name, univs1,
                                                                uu____18987,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____18972
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____18971;
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
                                                          uu____18970)
                                                         in
                                                      (name, uu____18949)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____18748
                                         in
                                      (match uu____18719 with
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
                             | uu____19228 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19360  ->
                             match uu____19360 with
                             | (name_doc,uu____19388,uu____19389) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19469  ->
                             match uu____19469 with
                             | (uu____19490,uu____19491,se) -> se))
                      in
                   let uu____19521 =
                     let uu____19528 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____19528 rng
                      in
                   (match uu____19521 with
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
                               (fun uu____19594  ->
                                  match uu____19594 with
                                  | (uu____19617,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____19668,tps,k,uu____19671,constrs)
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
                                  | uu____19690 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____19707  ->
                                 match uu____19707 with
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
      let uu____19750 =
        FStar_List.fold_left
          (fun uu____19785  ->
             fun b  ->
               match uu____19785 with
               | (env1,binders1) ->
                   let uu____19829 = desugar_binder env1 b  in
                   (match uu____19829 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19852 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____19852 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____19907 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____19750 with
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
          let uu____20008 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___108_20013  ->
                    match uu___108_20013 with
                    | FStar_Syntax_Syntax.Reflectable uu____20014 -> true
                    | uu____20015 -> false))
             in
          if uu____20008
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____20018 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____20018
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
                  let uu____20160 = desugar_binders monad_env eff_binders  in
                  match uu____20160 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____20199 =
                          let uu____20200 =
                            let uu____20207 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____20207  in
                          FStar_List.length uu____20200  in
                        uu____20199 = (Prims.parse_int "1")  in
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
                            (uu____20247,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____20249,uu____20250,uu____20251),uu____20252)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____20285 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____20286 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____20298 = name_of_eff_decl decl  in
                             FStar_List.mem uu____20298 mandatory_members)
                          eff_decls
                         in
                      (match uu____20286 with
                       | (mandatory_members_decls,actions) ->
                           let uu____20315 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____20344  ->
                                     fun decl  ->
                                       match uu____20344 with
                                       | (env2,out) ->
                                           let uu____20364 =
                                             desugar_decl env2 decl  in
                                           (match uu____20364 with
                                            | (env3,ses) ->
                                                let uu____20377 =
                                                  let uu____20380 =
                                                    FStar_List.hd ses  in
                                                  uu____20380 :: out  in
                                                (env3, uu____20377)))
                                  (env1, []))
                              in
                           (match uu____20315 with
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
                                              (uu____20448,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____20451,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____20452,
                                                                  (def,uu____20454)::
                                                                  (cps_type,uu____20456)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____20457;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____20458;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____20510 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____20510 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____20548 =
                                                     let uu____20549 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____20550 =
                                                       let uu____20551 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20551
                                                        in
                                                     let uu____20556 =
                                                       let uu____20557 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20557
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____20549;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____20550;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____20556
                                                     }  in
                                                   (uu____20548, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____20564,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____20567,defn),doc1)::[])
                                              when for_free ->
                                              let uu____20602 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____20602 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____20640 =
                                                     let uu____20641 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____20642 =
                                                       let uu____20643 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20643
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____20641;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____20642;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____20640, doc1))
                                          | uu____20650 ->
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
                                    let uu____20682 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____20682
                                     in
                                  let uu____20683 =
                                    let uu____20684 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____20684
                                     in
                                  ([], uu____20683)  in
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
                                      let uu____20701 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____20701)  in
                                    let uu____20708 =
                                      let uu____20709 =
                                        let uu____20710 =
                                          let uu____20711 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____20711
                                           in
                                        let uu____20720 = lookup1 "return"
                                           in
                                        let uu____20721 = lookup1 "bind"  in
                                        let uu____20722 =
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
                                            uu____20710;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____20720;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____20721;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____20722
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____20709
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____20708;
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
                                         (fun uu___109_20728  ->
                                            match uu___109_20728 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____20729 -> true
                                            | uu____20730 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____20744 =
                                       let uu____20745 =
                                         let uu____20746 =
                                           lookup1 "return_wp"  in
                                         let uu____20747 = lookup1 "bind_wp"
                                            in
                                         let uu____20748 =
                                           lookup1 "if_then_else"  in
                                         let uu____20749 = lookup1 "ite_wp"
                                            in
                                         let uu____20750 = lookup1 "stronger"
                                            in
                                         let uu____20751 = lookup1 "close_wp"
                                            in
                                         let uu____20752 = lookup1 "assert_p"
                                            in
                                         let uu____20753 = lookup1 "assume_p"
                                            in
                                         let uu____20754 = lookup1 "null_wp"
                                            in
                                         let uu____20755 = lookup1 "trivial"
                                            in
                                         let uu____20756 =
                                           if rr
                                           then
                                             let uu____20757 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____20757
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____20773 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____20775 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____20777 =
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
                                             uu____20746;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____20747;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____20748;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____20749;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____20750;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____20751;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____20752;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____20753;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____20754;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____20755;
                                           FStar_Syntax_Syntax.repr =
                                             uu____20756;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____20773;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____20775;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____20777
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____20745
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____20744;
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
                                          fun uu____20803  ->
                                            match uu____20803 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____20817 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____20817
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
                let uu____20841 = desugar_binders env1 eff_binders  in
                match uu____20841 with
                | (env2,binders) ->
                    let uu____20878 =
                      let uu____20897 = head_and_args defn  in
                      match uu____20897 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____20942 ->
                                let uu____20943 =
                                  let uu____20948 =
                                    let uu____20949 =
                                      let uu____20950 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____20950 " not found"
                                       in
                                    Prims.strcat "Effect " uu____20949  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____20948)
                                   in
                                FStar_Errors.raise_error uu____20943
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____20952 =
                            match FStar_List.rev args with
                            | (last_arg,uu____20982)::args_rev ->
                                let uu____20994 =
                                  let uu____20995 = unparen last_arg  in
                                  uu____20995.FStar_Parser_AST.tm  in
                                (match uu____20994 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____21023 -> ([], args))
                            | uu____21032 -> ([], args)  in
                          (match uu____20952 with
                           | (cattributes,args1) ->
                               let uu____21083 = desugar_args env2 args1  in
                               let uu____21092 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____21083, uu____21092))
                       in
                    (match uu____20878 with
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
                          (let uu____21148 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____21148 with
                           | (ed_binders,uu____21162,ed_binders_opening) ->
                               let sub1 uu____21175 =
                                 match uu____21175 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____21189 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____21189 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____21193 =
                                       let uu____21194 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____21194)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____21193
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____21203 =
                                   let uu____21204 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____21204
                                    in
                                 let uu____21219 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____21220 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____21221 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____21222 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____21223 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____21224 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____21225 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____21226 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____21227 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____21228 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____21229 =
                                   let uu____21230 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____21230
                                    in
                                 let uu____21245 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____21246 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____21247 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____21255 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____21256 =
                                          let uu____21257 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21257
                                           in
                                        let uu____21272 =
                                          let uu____21273 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21273
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____21255;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____21256;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____21272
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
                                     uu____21203;
                                   FStar_Syntax_Syntax.ret_wp = uu____21219;
                                   FStar_Syntax_Syntax.bind_wp = uu____21220;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____21221;
                                   FStar_Syntax_Syntax.ite_wp = uu____21222;
                                   FStar_Syntax_Syntax.stronger = uu____21223;
                                   FStar_Syntax_Syntax.close_wp = uu____21224;
                                   FStar_Syntax_Syntax.assert_p = uu____21225;
                                   FStar_Syntax_Syntax.assume_p = uu____21226;
                                   FStar_Syntax_Syntax.null_wp = uu____21227;
                                   FStar_Syntax_Syntax.trivial = uu____21228;
                                   FStar_Syntax_Syntax.repr = uu____21229;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____21245;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____21246;
                                   FStar_Syntax_Syntax.actions = uu____21247;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____21290 =
                                     let uu____21291 =
                                       let uu____21298 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____21298
                                        in
                                     FStar_List.length uu____21291  in
                                   uu____21290 = (Prims.parse_int "1")  in
                                 let uu____21323 =
                                   let uu____21326 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____21326 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____21323;
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
                                             let uu____21348 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____21348
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____21350 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____21350
                                 then
                                   let reflect_lid =
                                     let uu____21354 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____21354
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
    let uu____21364 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____21364 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____21415 ->
              let uu____21416 =
                let uu____21417 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____21417
                 in
              Prims.strcat "\n  " uu____21416
          | uu____21418 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____21431  ->
               match uu____21431 with
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
          let uu____21449 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____21449
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____21451 =
          let uu____21460 = FStar_Syntax_Syntax.as_arg arg  in [uu____21460]
           in
        FStar_Syntax_Util.mk_app fv uu____21451

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____21485 = desugar_decl_noattrs env d  in
      match uu____21485 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____21503 = mk_comment_attr d  in uu____21503 :: attrs1  in
          let uu____21504 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___136_21508 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___136_21508.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___136_21508.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___136_21508.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___136_21508.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____21504)

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
      | FStar_Parser_AST.Fsdoc uu____21534 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____21542 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____21542, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____21579  ->
                 match uu____21579 with | (x,uu____21587) -> x) tcs
             in
          let uu____21592 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____21592 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____21614;
                    FStar_Parser_AST.prange = uu____21615;_},uu____21616)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____21625;
                    FStar_Parser_AST.prange = uu____21626;_},uu____21627)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____21642;
                         FStar_Parser_AST.prange = uu____21643;_},uu____21644);
                    FStar_Parser_AST.prange = uu____21645;_},uu____21646)::[]
                   -> false
               | (p,uu____21674)::[] ->
                   let uu____21683 = is_app_pattern p  in
                   Prims.op_Negation uu____21683
               | uu____21684 -> false)
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
            let uu____21757 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____21757 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____21769 =
                     let uu____21770 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____21770.FStar_Syntax_Syntax.n  in
                   match uu____21769 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____21780) ->
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
                         | uu____21813::uu____21814 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____21817 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___110_21832  ->
                                     match uu___110_21832 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____21835;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____21836;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____21837;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____21838;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____21839;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____21840;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____21841;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____21853;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____21854;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____21855;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____21856;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____21857;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____21858;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____21872 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____21903  ->
                                   match uu____21903 with
                                   | (uu____21916,(uu____21917,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____21872
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____21935 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____21935
                         then
                           let uu____21938 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___137_21952 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___138_21954 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___138_21954.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___138_21954.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___137_21952.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___137_21952.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___137_21952.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___137_21952.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___137_21952.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___137_21952.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____21938)
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
                   | uu____21981 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____21987 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____22006 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____21987 with
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
                       let uu___139_22042 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___139_22042.FStar_Parser_AST.prange)
                       }
                   | uu____22049 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___140_22056 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___140_22056.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___140_22056.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___140_22056.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____22092 id1 =
                   match uu____22092 with
                   | (env1,ses) ->
                       let main =
                         let uu____22113 =
                           let uu____22114 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____22114  in
                         FStar_Parser_AST.mk_term uu____22113
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
                       let uu____22164 = desugar_decl env1 id_decl  in
                       (match uu____22164 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____22182 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____22182 FStar_Util.set_elements
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
            let uu____22205 = close_fun env t  in
            desugar_term env uu____22205  in
          let quals1 =
            let uu____22209 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____22209
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____22215 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____22215;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____22223 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____22223 with
           | (t,uu____22237) ->
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
            let uu____22267 =
              let uu____22274 = FStar_Syntax_Syntax.null_binder t  in
              [uu____22274]  in
            let uu____22287 =
              let uu____22290 =
                let uu____22291 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____22291  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____22290
               in
            FStar_Syntax_Util.arrow uu____22267 uu____22287  in
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
            let uu____22352 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____22352 with
            | FStar_Pervasives_Native.None  ->
                let uu____22355 =
                  let uu____22360 =
                    let uu____22361 =
                      let uu____22362 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____22362 " not found"  in
                    Prims.strcat "Effect name " uu____22361  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____22360)  in
                FStar_Errors.raise_error uu____22355
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____22366 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____22408 =
                  let uu____22417 =
                    let uu____22424 = desugar_term env t  in
                    ([], uu____22424)  in
                  FStar_Pervasives_Native.Some uu____22417  in
                (uu____22408, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____22457 =
                  let uu____22466 =
                    let uu____22473 = desugar_term env wp  in
                    ([], uu____22473)  in
                  FStar_Pervasives_Native.Some uu____22466  in
                let uu____22482 =
                  let uu____22491 =
                    let uu____22498 = desugar_term env t  in
                    ([], uu____22498)  in
                  FStar_Pervasives_Native.Some uu____22491  in
                (uu____22457, uu____22482)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____22524 =
                  let uu____22533 =
                    let uu____22540 = desugar_term env t  in
                    ([], uu____22540)  in
                  FStar_Pervasives_Native.Some uu____22533  in
                (FStar_Pervasives_Native.None, uu____22524)
             in
          (match uu____22366 with
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
            let uu____22618 =
              let uu____22619 =
                let uu____22626 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____22626, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____22619  in
            {
              FStar_Syntax_Syntax.sigel = uu____22618;
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
      let uu____22652 =
        FStar_List.fold_left
          (fun uu____22672  ->
             fun d  ->
               match uu____22672 with
               | (env1,sigelts) ->
                   let uu____22692 = desugar_decl env1 d  in
                   (match uu____22692 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____22652 with
      | (env1,sigelts) ->
          let rec forward acc uu___112_22737 =
            match uu___112_22737 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____22751,FStar_Syntax_Syntax.Sig_let uu____22752) ->
                     let uu____22765 =
                       let uu____22768 =
                         let uu___141_22769 = se2  in
                         let uu____22770 =
                           let uu____22773 =
                             FStar_List.filter
                               (fun uu___111_22787  ->
                                  match uu___111_22787 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____22791;
                                           FStar_Syntax_Syntax.vars =
                                             uu____22792;_},uu____22793);
                                      FStar_Syntax_Syntax.pos = uu____22794;
                                      FStar_Syntax_Syntax.vars = uu____22795;_}
                                      when
                                      let uu____22818 =
                                        let uu____22819 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____22819
                                         in
                                      uu____22818 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____22820 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____22773
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___141_22769.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___141_22769.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___141_22769.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___141_22769.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____22770
                         }  in
                       uu____22768 :: se1 :: acc  in
                     forward uu____22765 sigelts1
                 | uu____22825 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____22833 = forward [] sigelts  in (env1, uu____22833)
  
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
      let uu____22875 =
        let uu____22888 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____22905  ->
               match uu____22905 with
               | ({ FStar_Syntax_Syntax.ppname = uu____22914;
                    FStar_Syntax_Syntax.index = uu____22915;
                    FStar_Syntax_Syntax.sort = t;_},uu____22917)
                   ->
                   let uu____22920 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____22920) uu____22888
         in
      FStar_All.pipe_right bs uu____22875  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____22934 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____22951 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____22977 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____22998,uu____22999,bs,t,uu____23002,uu____23003)
                            ->
                            let uu____23012 = bs_univnames bs  in
                            let uu____23015 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____23012 uu____23015
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____23018,uu____23019,t,uu____23021,uu____23022,uu____23023)
                            -> FStar_Syntax_Free.univnames t
                        | uu____23028 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____22977 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___142_23036 = s  in
        let uu____23037 =
          let uu____23038 =
            let uu____23047 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____23065,bs,t,lids1,lids2) ->
                          let uu___143_23078 = se  in
                          let uu____23079 =
                            let uu____23080 =
                              let uu____23097 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____23098 =
                                let uu____23099 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____23099 t  in
                              (lid, uvs, uu____23097, uu____23098, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____23080
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____23079;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___143_23078.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___143_23078.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___143_23078.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___143_23078.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____23111,t,tlid,n1,lids1) ->
                          let uu___144_23120 = se  in
                          let uu____23121 =
                            let uu____23122 =
                              let uu____23137 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____23137, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____23122  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____23121;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___144_23120.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___144_23120.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___144_23120.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___144_23120.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____23140 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____23047, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____23038  in
        {
          FStar_Syntax_Syntax.sigel = uu____23037;
          FStar_Syntax_Syntax.sigrng =
            (uu___142_23036.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___142_23036.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___142_23036.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___142_23036.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23146,t) ->
        let uvs =
          let uu____23149 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____23149 FStar_Util.set_elements  in
        let uu___145_23154 = s  in
        let uu____23155 =
          let uu____23156 =
            let uu____23163 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____23163)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____23156  in
        {
          FStar_Syntax_Syntax.sigel = uu____23155;
          FStar_Syntax_Syntax.sigrng =
            (uu___145_23154.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___145_23154.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___145_23154.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___145_23154.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____23185 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23188 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____23195) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____23224,(FStar_Util.Inl t,uu____23226),uu____23227)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____23274,(FStar_Util.Inr c,uu____23276),uu____23277)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____23324 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____23325,(FStar_Util.Inl t,uu____23327),uu____23328) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____23375,(FStar_Util.Inr c,uu____23377),uu____23378) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____23425 -> empty_set  in
          FStar_Util.set_union uu____23185 uu____23188  in
        let all_lb_univs =
          let uu____23429 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____23445 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____23445) empty_set)
             in
          FStar_All.pipe_right uu____23429 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___146_23455 = s  in
        let uu____23456 =
          let uu____23457 =
            let uu____23464 =
              let uu____23465 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___147_23477 = lb  in
                        let uu____23478 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____23481 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___147_23477.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____23478;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___147_23477.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____23481;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___147_23477.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___147_23477.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____23465)  in
            (uu____23464, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____23457  in
        {
          FStar_Syntax_Syntax.sigel = uu____23456;
          FStar_Syntax_Syntax.sigrng =
            (uu___146_23455.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___146_23455.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___146_23455.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___146_23455.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____23489,fml) ->
        let uvs =
          let uu____23492 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____23492 FStar_Util.set_elements  in
        let uu___148_23497 = s  in
        let uu____23498 =
          let uu____23499 =
            let uu____23506 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____23506)  in
          FStar_Syntax_Syntax.Sig_assume uu____23499  in
        {
          FStar_Syntax_Syntax.sigel = uu____23498;
          FStar_Syntax_Syntax.sigrng =
            (uu___148_23497.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___148_23497.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___148_23497.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___148_23497.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____23508,bs,c,flags1) ->
        let uvs =
          let uu____23517 =
            let uu____23520 = bs_univnames bs  in
            let uu____23523 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____23520 uu____23523  in
          FStar_All.pipe_right uu____23517 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___149_23531 = s  in
        let uu____23532 =
          let uu____23533 =
            let uu____23546 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____23547 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____23546, uu____23547, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____23533  in
        {
          FStar_Syntax_Syntax.sigel = uu____23532;
          FStar_Syntax_Syntax.sigrng =
            (uu___149_23531.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___149_23531.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___149_23531.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___149_23531.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____23550 -> s
  
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
          | (FStar_Pervasives_Native.None ,uu____23585) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____23589;
               FStar_Syntax_Syntax.exports = uu____23590;
               FStar_Syntax_Syntax.is_interface = uu____23591;_},FStar_Parser_AST.Module
             (current_lid,uu____23593)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____23601) ->
              let uu____23604 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____23604
           in
        let uu____23609 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____23645 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23645, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____23662 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23662, mname, decls, false)
           in
        match uu____23609 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____23692 = desugar_decls env2 decls  in
            (match uu____23692 with
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
          let uu____23757 =
            (FStar_Options.interactive ()) &&
              (let uu____23759 =
                 let uu____23760 =
                   let uu____23761 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____23761  in
                 FStar_Util.get_file_extension uu____23760  in
               FStar_List.mem uu____23759 ["fsti"; "fsi"])
             in
          if uu____23757 then as_interface m else m  in
        let uu____23765 = desugar_modul_common curmod env m1  in
        match uu____23765 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____23780 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____23800 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____23800 with
      | (env1,modul,pop_when_done) ->
          let uu____23814 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____23814 with
           | (env2,modul1) ->
               ((let uu____23826 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____23826
                 then
                   let uu____23827 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____23827
                 else ());
                (let uu____23829 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____23829, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____23847 = desugar_modul env modul  in
      match uu____23847 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____23878 = desugar_decls env decls  in
      match uu____23878 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____23920 = desugar_partial_modul modul env a_modul  in
        match uu____23920 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____24006 ->
                  let t =
                    let uu____24014 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____24014  in
                  let uu____24025 =
                    let uu____24026 = FStar_Syntax_Subst.compress t  in
                    uu____24026.FStar_Syntax_Syntax.n  in
                  (match uu____24025 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____24036,uu____24037)
                       -> bs1
                   | uu____24058 -> failwith "Impossible")
               in
            let uu____24065 =
              let uu____24072 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____24072
                FStar_Syntax_Syntax.t_unit
               in
            match uu____24065 with
            | (binders,uu____24074,binders_opening) ->
                let erase_term t =
                  let uu____24082 =
                    let uu____24083 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____24083  in
                  FStar_Syntax_Subst.close binders uu____24082  in
                let erase_tscheme uu____24101 =
                  match uu____24101 with
                  | (us,t) ->
                      let t1 =
                        let uu____24121 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____24121 t  in
                      let uu____24124 =
                        let uu____24125 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____24125  in
                      ([], uu____24124)
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
                    | uu____24144 ->
                        let bs =
                          let uu____24152 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____24152  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____24184 =
                          let uu____24185 =
                            let uu____24188 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____24188  in
                          uu____24185.FStar_Syntax_Syntax.n  in
                        (match uu____24184 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____24190,uu____24191) -> bs1
                         | uu____24212 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____24219 =
                      let uu____24220 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____24220  in
                    FStar_Syntax_Subst.close binders uu____24219  in
                  let uu___150_24221 = action  in
                  let uu____24222 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____24223 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___150_24221.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___150_24221.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____24222;
                    FStar_Syntax_Syntax.action_typ = uu____24223
                  }  in
                let uu___151_24224 = ed  in
                let uu____24225 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____24226 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____24227 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____24228 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____24229 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____24230 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____24231 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____24232 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____24233 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____24234 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____24235 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____24236 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____24237 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____24238 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____24239 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____24240 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___151_24224.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___151_24224.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____24225;
                  FStar_Syntax_Syntax.signature = uu____24226;
                  FStar_Syntax_Syntax.ret_wp = uu____24227;
                  FStar_Syntax_Syntax.bind_wp = uu____24228;
                  FStar_Syntax_Syntax.if_then_else = uu____24229;
                  FStar_Syntax_Syntax.ite_wp = uu____24230;
                  FStar_Syntax_Syntax.stronger = uu____24231;
                  FStar_Syntax_Syntax.close_wp = uu____24232;
                  FStar_Syntax_Syntax.assert_p = uu____24233;
                  FStar_Syntax_Syntax.assume_p = uu____24234;
                  FStar_Syntax_Syntax.null_wp = uu____24235;
                  FStar_Syntax_Syntax.trivial = uu____24236;
                  FStar_Syntax_Syntax.repr = uu____24237;
                  FStar_Syntax_Syntax.return_repr = uu____24238;
                  FStar_Syntax_Syntax.bind_repr = uu____24239;
                  FStar_Syntax_Syntax.actions = uu____24240;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___151_24224.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___152_24256 = se  in
                  let uu____24257 =
                    let uu____24258 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____24258  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24257;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___152_24256.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___152_24256.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___152_24256.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___152_24256.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___153_24262 = se  in
                  let uu____24263 =
                    let uu____24264 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24264
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24263;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___153_24262.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___153_24262.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___153_24262.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___153_24262.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____24266 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____24267 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____24267 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____24279 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____24279
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____24281 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____24281)
  