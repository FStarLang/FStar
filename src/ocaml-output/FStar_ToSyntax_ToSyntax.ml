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
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.binder,FStar_Syntax_DsEnv.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun imp  ->
      fun uu___89_1746  ->
        match uu___89_1746 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1762 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1762, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1767 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1767 with
             | (env1,a1) ->
                 (((let uu___113_1787 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___113_1787.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___113_1787.FStar_Syntax_Syntax.index);
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
  fun uu____1816  ->
    match uu____1816 with
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
      let uu____1890 =
        let uu____1905 =
          let uu____1906 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1906  in
        let uu____1907 =
          let uu____1916 =
            let uu____1923 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1923)  in
          [uu____1916]  in
        (uu____1905, uu____1907)  in
      FStar_Syntax_Syntax.Tm_app uu____1890  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1958 =
        let uu____1973 =
          let uu____1974 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1974  in
        let uu____1975 =
          let uu____1984 =
            let uu____1991 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1991)  in
          [uu____1984]  in
        (uu____1973, uu____1975)  in
      FStar_Syntax_Syntax.Tm_app uu____1958  in
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
          let uu____2040 =
            let uu____2055 =
              let uu____2056 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2056  in
            let uu____2057 =
              let uu____2066 =
                let uu____2073 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2073)  in
              let uu____2076 =
                let uu____2085 =
                  let uu____2092 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2092)  in
                [uu____2085]  in
              uu____2066 :: uu____2076  in
            (uu____2055, uu____2057)  in
          FStar_Syntax_Syntax.Tm_app uu____2040  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___90_2125  ->
    match uu___90_2125 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2126 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2138 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2138)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2157 =
      let uu____2158 = unparen t  in uu____2158.FStar_Parser_AST.tm  in
    match uu____2157 with
    | FStar_Parser_AST.Wild  ->
        let uu____2163 =
          let uu____2164 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2164  in
        FStar_Util.Inr uu____2163
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2175)) ->
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
             let uu____2240 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2240
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2251 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2251
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2262 =
               let uu____2267 =
                 let uu____2268 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2268
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2267)
                in
             FStar_Errors.raise_error uu____2262 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2273 ->
        let rec aux t1 univargs =
          let uu____2307 =
            let uu____2308 = unparen t1  in uu____2308.FStar_Parser_AST.tm
             in
          match uu____2307 with
          | FStar_Parser_AST.App (t2,targ,uu____2315) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___91_2338  ->
                     match uu___91_2338 with
                     | FStar_Util.Inr uu____2343 -> true
                     | uu____2344 -> false) univargs
              then
                let uu____2349 =
                  let uu____2350 =
                    FStar_List.map
                      (fun uu___92_2359  ->
                         match uu___92_2359 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2350  in
                FStar_Util.Inr uu____2349
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___93_2376  ->
                        match uu___93_2376 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2382 -> failwith "impossible")
                     univargs
                    in
                 let uu____2383 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2383)
          | uu____2389 ->
              let uu____2390 =
                let uu____2395 =
                  let uu____2396 =
                    let uu____2397 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2397 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2396  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2395)  in
              FStar_Errors.raise_error uu____2390 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2406 ->
        let uu____2407 =
          let uu____2412 =
            let uu____2413 =
              let uu____2414 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2414 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2413  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2412)  in
        FStar_Errors.raise_error uu____2407 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____2447 ->
        let uu____2470 =
          let uu____2475 =
            let uu____2476 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____2476
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____2475)  in
        FStar_Errors.raise_error uu____2470 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____2486 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2486) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2514 = FStar_List.hd fields  in
        match uu____2514 with
        | (f,uu____2524) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2536 =
                match uu____2536 with
                | (f',uu____2542) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2544 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____2544
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
              (let uu____2548 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2548);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2903 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2910 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2911 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2913,pats1) ->
                let aux out uu____2951 =
                  match uu____2951 with
                  | (p2,uu____2963) ->
                      let intersection =
                        let uu____2971 = pat_vars p2  in
                        FStar_Util.set_intersect uu____2971 out  in
                      let uu____2974 = FStar_Util.set_is_empty intersection
                         in
                      if uu____2974
                      then
                        let uu____2977 = pat_vars p2  in
                        FStar_Util.set_union out uu____2977
                      else
                        (let duplicate_bv =
                           let uu____2982 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____2982  in
                         let uu____2985 =
                           let uu____2990 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____2990)
                            in
                         FStar_Errors.raise_error uu____2985 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3010 = pat_vars p1  in
              FStar_All.pipe_right uu____3010 (fun a238  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3032 =
                  let uu____3033 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3033  in
                if uu____3032
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3040 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3040  in
                   let first_nonlinear_var =
                     let uu____3044 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3044  in
                   let uu____3047 =
                     let uu____3052 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3052)  in
                   FStar_Errors.raise_error uu____3047 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3056) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3057) -> ()
         | (true ,uu____3064) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3087 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____3087 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3101 ->
               let uu____3104 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____3104 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3216 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____3232 =
                 let uu____3233 =
                   let uu____3234 =
                     let uu____3241 =
                       let uu____3242 =
                         let uu____3247 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____3247, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____3242  in
                     (uu____3241, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____3234  in
                 {
                   FStar_Parser_AST.pat = uu____3233;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____3232
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____3264 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____3265 = aux loc env1 p2  in
                 match uu____3265 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___114_3323 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___115_3328 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___115_3328.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___115_3328.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___114_3323.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___116_3330 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___117_3335 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___117_3335.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___117_3335.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___116_3330.FStar_Syntax_Syntax.p)
                           }
                       | uu____3336 when top -> p4
                       | uu____3337 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____3340 =
                       match binder with
                       | LetBinder uu____3353 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____3373 = close_fun env1 t  in
                             desugar_term env1 uu____3373  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____3375 -> true)
                            then
                              (let uu____3376 =
                                 let uu____3381 =
                                   let uu____3382 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____3383 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____3384 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3382 uu____3383 uu____3384
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3381)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3376)
                            else ();
                            (let uu____3386 = annot_pat_var p3 t1  in
                             (uu____3386,
                               (LocalBinder
                                  ((let uu___118_3392 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___118_3392.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___118_3392.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____3340 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3414 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3414, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3425 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3425, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3446 = resolvex loc env1 x  in
               (match uu____3446 with
                | (loc1,env2,xbv) ->
                    let uu____3468 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3468, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3489 = resolvex loc env1 x  in
               (match uu____3489 with
                | (loc1,env2,xbv) ->
                    let uu____3511 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3511, imp))
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
               let uu____3523 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3523, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3547;_},args)
               ->
               let uu____3553 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3594  ->
                        match uu____3594 with
                        | (loc1,env2,args1) ->
                            let uu____3642 = aux loc1 env2 arg  in
                            (match uu____3642 with
                             | (loc2,env3,uu____3671,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____3553 with
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
                    let uu____3741 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3741, false))
           | FStar_Parser_AST.PatApp uu____3758 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3780 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3813  ->
                        match uu____3813 with
                        | (loc1,env2,pats1) ->
                            let uu____3845 = aux loc1 env2 pat  in
                            (match uu____3845 with
                             | (loc2,env3,uu____3870,pat1,uu____3872) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3780 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3915 =
                        let uu____3918 =
                          let uu____3925 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3925  in
                        let uu____3926 =
                          let uu____3927 =
                            let uu____3940 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3940, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3927  in
                        FStar_All.pipe_left uu____3918 uu____3926  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3972 =
                               let uu____3973 =
                                 let uu____3986 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3986, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3973  in
                             FStar_All.pipe_left (pos_r r) uu____3972) pats1
                        uu____3915
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
               let uu____4030 =
                 FStar_List.fold_left
                   (fun uu____4070  ->
                      fun p2  ->
                        match uu____4070 with
                        | (loc1,env2,pats) ->
                            let uu____4119 = aux loc1 env2 p2  in
                            (match uu____4119 with
                             | (loc2,env3,uu____4148,pat,uu____4150) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4030 with
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
                    let uu____4245 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____4245 with
                     | (constr,uu____4267) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____4270 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____4272 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____4272, false)))
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
                      (fun uu____4343  ->
                         match uu____4343 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4373  ->
                         match uu____4373 with
                         | (f,uu____4379) ->
                             let uu____4380 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4406  ->
                                       match uu____4406 with
                                       | (g,uu____4412) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____4380 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4417,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____4424 =
                   let uu____4425 =
                     let uu____4432 =
                       let uu____4433 =
                         let uu____4434 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____4434  in
                       FStar_Parser_AST.mk_pattern uu____4433
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____4432, args)  in
                   FStar_Parser_AST.PatApp uu____4425  in
                 FStar_Parser_AST.mk_pattern uu____4424
                   p1.FStar_Parser_AST.prange
                  in
               let uu____4437 = aux loc env1 app  in
               (match uu____4437 with
                | (env2,e,b,p2,uu____4466) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4494 =
                            let uu____4495 =
                              let uu____4508 =
                                let uu___119_4509 = fv  in
                                let uu____4510 =
                                  let uu____4513 =
                                    let uu____4514 =
                                      let uu____4521 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4521)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4514
                                     in
                                  FStar_Pervasives_Native.Some uu____4513  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___119_4509.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___119_4509.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4510
                                }  in
                              (uu____4508, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____4495  in
                          FStar_All.pipe_left pos uu____4494
                      | uu____4548 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4602 = aux' true loc env1 p2  in
               (match uu____4602 with
                | (loc1,env2,var,p3,uu____4629) ->
                    let uu____4634 =
                      FStar_List.fold_left
                        (fun uu____4666  ->
                           fun p4  ->
                             match uu____4666 with
                             | (loc2,env3,ps1) ->
                                 let uu____4699 = aux' true loc2 env3 p4  in
                                 (match uu____4699 with
                                  | (loc3,env4,uu____4724,p5,uu____4726) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____4634 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4777 ->
               let uu____4778 = aux' true loc env1 p1  in
               (match uu____4778 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4818 = aux_maybe_or env p  in
         match uu____4818 with
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
            let uu____4879 =
              let uu____4880 =
                let uu____4891 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4891,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4880  in
            (env, uu____4879, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4919 =
                  let uu____4920 =
                    let uu____4925 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4925, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4920  in
                mklet uu____4919
            | FStar_Parser_AST.PatVar (x,uu____4927) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4933);
                   FStar_Parser_AST.prange = uu____4934;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4954 =
                  let uu____4955 =
                    let uu____4966 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____4967 =
                      let uu____4974 = desugar_term env t  in
                      (uu____4974, tacopt1)  in
                    (uu____4966, uu____4967)  in
                  LetBinder uu____4955  in
                (env, uu____4954, [])
            | uu____4985 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4995 = desugar_data_pat env p is_mut  in
             match uu____4995 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5024;
                       FStar_Syntax_Syntax.p = uu____5025;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5030;
                       FStar_Syntax_Syntax.p = uu____5031;_}::[] -> []
                   | uu____5036 -> p1  in
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
  fun uu____5043  ->
    fun env  ->
      fun pat  ->
        let uu____5046 = desugar_data_pat env pat false  in
        match uu____5046 with | (env1,uu____5062,pat1) -> (env1, pat1)

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
      let uu____5081 = desugar_term_aq env e  in
      match uu____5081 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____5098 = desugar_typ_aq env e  in
      match uu____5098 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5108  ->
        fun range  ->
          match uu____5108 with
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
              ((let uu____5118 =
                  let uu____5119 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5119  in
                if uu____5118
                then
                  let uu____5120 =
                    let uu____5125 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5125)  in
                  FStar_Errors.log_issue range uu____5120
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
                  let uu____5130 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____5130 range  in
                let lid1 =
                  let uu____5134 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____5134 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____5144) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5153 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____5153 range  in
                           let private_fv =
                             let uu____5155 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5155 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___120_5156 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___120_5156.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___120_5156.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5157 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5164 =
                        let uu____5169 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5169)
                         in
                      FStar_Errors.raise_error uu____5164 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____5185 =
                  let uu____5192 =
                    let uu____5193 =
                      let uu____5208 =
                        let uu____5217 =
                          let uu____5224 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____5224)  in
                        [uu____5217]  in
                      (lid1, uu____5208)  in
                    FStar_Syntax_Syntax.Tm_app uu____5193  in
                  FStar_Syntax_Syntax.mk uu____5192  in
                uu____5185 FStar_Pervasives_Native.None range))

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
            let uu____5263 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____5263 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____5312;
                              FStar_Syntax_Syntax.vars = uu____5313;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5336 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5336 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5344 =
                                 let uu____5345 =
                                   let uu____5348 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____5348  in
                                 uu____5345.FStar_Syntax_Syntax.n  in
                               match uu____5344 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____5364))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5365 -> msg
                             else msg  in
                           let uu____5367 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5367
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5370 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5370 " is deprecated"  in
                           let uu____5371 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5371
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5372 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____5377 =
                      let uu____5378 =
                        let uu____5385 = mk_ref_read tm1  in
                        (uu____5385,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____5378  in
                    FStar_All.pipe_left mk1 uu____5377
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____5403 =
          let uu____5404 = unparen t  in uu____5404.FStar_Parser_AST.tm  in
        match uu____5403 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5405; FStar_Ident.ident = uu____5406;
              FStar_Ident.nsstr = uu____5407; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5410 ->
            let uu____5411 =
              let uu____5416 =
                let uu____5417 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5417  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5416)  in
            FStar_Errors.raise_error uu____5411 t.FStar_Parser_AST.range
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
          let uu___121_5512 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___121_5512.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___121_5512.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5515 =
          let uu____5516 = unparen top  in uu____5516.FStar_Parser_AST.tm  in
        match uu____5515 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5533 ->
            let uu____5540 = desugar_formula env top  in (uu____5540, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____5557 = desugar_formula env t  in (uu____5557, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____5574 = desugar_formula env t  in (uu____5574, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____5608 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____5608, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5620 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____5620, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____5642 =
                let uu____5643 =
                  let uu____5650 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____5650, args)  in
                FStar_Parser_AST.Op uu____5643  in
              FStar_Parser_AST.mk_term uu____5642 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____5653 =
              let uu____5654 =
                let uu____5655 =
                  let uu____5662 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____5662, [e])  in
                FStar_Parser_AST.Op uu____5655  in
              FStar_Parser_AST.mk_term uu____5654 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____5653
        | FStar_Parser_AST.Op (op_star,uu____5666::uu____5667::[]) when
            (let uu____5672 = FStar_Ident.text_of_id op_star  in
             uu____5672 = "*") &&
              (let uu____5674 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5674 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5689;_},t1::t2::[])
                  ->
                  let uu____5694 = flatten1 t1  in
                  FStar_List.append uu____5694 [t2]
              | uu____5697 -> [t]  in
            let uu____5698 =
              let uu____5707 =
                let uu____5714 =
                  let uu____5717 = unparen top  in flatten1 uu____5717  in
                FStar_All.pipe_right uu____5714
                  (FStar_List.map
                     (fun t  ->
                        let uu____5736 = desugar_typ_aq env t  in
                        match uu____5736 with
                        | (t',aq) ->
                            let uu____5747 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5747, aq)))
                 in
              FStar_All.pipe_right uu____5707 FStar_List.unzip  in
            (match uu____5698 with
             | (targs,aqs) ->
                 let uu____5776 =
                   let uu____5781 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5781
                    in
                 (match uu____5776 with
                  | (tup,uu____5791) ->
                      let uu____5792 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5792, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5810 =
              let uu____5813 =
                let uu____5816 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5816  in
              FStar_All.pipe_left setpos uu____5813  in
            (uu____5810, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5842 =
              let uu____5847 =
                let uu____5848 =
                  let uu____5849 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____5849 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____5848  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5847)  in
            FStar_Errors.raise_error uu____5842 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5860 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5860 with
             | FStar_Pervasives_Native.None  ->
                 let uu____5867 =
                   let uu____5872 =
                     let uu____5873 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5873
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5872)
                    in
                 FStar_Errors.raise_error uu____5867
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5883 =
                     let uu____5898 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____5940 = desugar_term_aq env t  in
                               match uu____5940 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____5898 FStar_List.unzip  in
                   (match uu____5883 with
                    | (args1,aqs) ->
                        let uu____6023 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6023, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6059)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6074 =
              let uu___122_6075 = top  in
              let uu____6076 =
                let uu____6077 =
                  let uu____6084 =
                    let uu___123_6085 = top  in
                    let uu____6086 =
                      let uu____6087 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6087  in
                    {
                      FStar_Parser_AST.tm = uu____6086;
                      FStar_Parser_AST.range =
                        (uu___123_6085.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___123_6085.FStar_Parser_AST.level)
                    }  in
                  (uu____6084, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6077  in
              {
                FStar_Parser_AST.tm = uu____6076;
                FStar_Parser_AST.range =
                  (uu___122_6075.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___122_6075.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6074
        | FStar_Parser_AST.Construct (n1,(a,uu____6090)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6106 =
                let uu___124_6107 = top  in
                let uu____6108 =
                  let uu____6109 =
                    let uu____6116 =
                      let uu___125_6117 = top  in
                      let uu____6118 =
                        let uu____6119 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____6119  in
                      {
                        FStar_Parser_AST.tm = uu____6118;
                        FStar_Parser_AST.range =
                          (uu___125_6117.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___125_6117.FStar_Parser_AST.level)
                      }  in
                    (uu____6116, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____6109  in
                {
                  FStar_Parser_AST.tm = uu____6108;
                  FStar_Parser_AST.range =
                    (uu___124_6107.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___124_6107.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____6106))
        | FStar_Parser_AST.Construct (n1,(a,uu____6122)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6137 =
              let uu___126_6138 = top  in
              let uu____6139 =
                let uu____6140 =
                  let uu____6147 =
                    let uu___127_6148 = top  in
                    let uu____6149 =
                      let uu____6150 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6150  in
                    {
                      FStar_Parser_AST.tm = uu____6149;
                      FStar_Parser_AST.range =
                        (uu___127_6148.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___127_6148.FStar_Parser_AST.level)
                    }  in
                  (uu____6147, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6140  in
              {
                FStar_Parser_AST.tm = uu____6139;
                FStar_Parser_AST.range =
                  (uu___126_6138.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___126_6138.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6137
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6151; FStar_Ident.ident = uu____6152;
              FStar_Ident.nsstr = uu____6153; FStar_Ident.str = "Type0";_}
            ->
            let uu____6156 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____6156, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6171; FStar_Ident.ident = uu____6172;
              FStar_Ident.nsstr = uu____6173; FStar_Ident.str = "Type";_}
            ->
            let uu____6176 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____6176, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6191; FStar_Ident.ident = uu____6192;
               FStar_Ident.nsstr = uu____6193; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____6211 =
              let uu____6214 =
                let uu____6215 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____6215  in
              mk1 uu____6214  in
            (uu____6211, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6228; FStar_Ident.ident = uu____6229;
              FStar_Ident.nsstr = uu____6230; FStar_Ident.str = "Effect";_}
            ->
            let uu____6233 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____6233, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6248; FStar_Ident.ident = uu____6249;
              FStar_Ident.nsstr = uu____6250; FStar_Ident.str = "True";_}
            ->
            let uu____6253 =
              let uu____6254 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6254
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6253, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6265; FStar_Ident.ident = uu____6266;
              FStar_Ident.nsstr = uu____6267; FStar_Ident.str = "False";_}
            ->
            let uu____6270 =
              let uu____6271 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6271
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6270, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____6284;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____6286 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____6286 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____6295 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_defined_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____6295, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____6306 =
                    let uu____6307 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____6307 txt
                     in
                  failwith uu____6306))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6314 = desugar_name mk1 setpos env true l  in
              (uu____6314, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6327 = desugar_name mk1 setpos env true l  in
              (uu____6327, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____6348 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____6348 with
                | FStar_Pervasives_Native.Some uu____6357 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____6362 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____6362 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6376 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____6393 =
                    let uu____6394 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____6394  in
                  (uu____6393, noaqs)
              | uu____6405 ->
                  let uu____6412 =
                    let uu____6417 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6417)  in
                  FStar_Errors.raise_error uu____6412
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6424 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____6424 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6431 =
                    let uu____6436 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6436)
                     in
                  FStar_Errors.raise_error uu____6431
                    top.FStar_Parser_AST.range
              | uu____6441 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____6445 = desugar_name mk1 setpos env true lid'  in
                  (uu____6445, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6471 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6471 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6502 ->
                       let uu____6509 =
                         FStar_Util.take
                           (fun uu____6533  ->
                              match uu____6533 with
                              | (uu____6538,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____6509 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____6583 =
                              let uu____6598 =
                                FStar_List.map
                                  (fun uu____6631  ->
                                     match uu____6631 with
                                     | (t,imp) ->
                                         let uu____6648 =
                                           desugar_term_aq env t  in
                                         (match uu____6648 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____6598
                                FStar_List.unzip
                               in
                            (match uu____6583 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____6741 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____6741, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____6771 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____6771 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6778 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6789 =
              FStar_List.fold_left
                (fun uu____6834  ->
                   fun b  ->
                     match uu____6834 with
                     | (env1,tparams,typs) ->
                         let uu____6891 = desugar_binder env1 b  in
                         (match uu____6891 with
                          | (xopt,t1) ->
                              let uu____6920 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6929 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6929)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6920 with
                               | (env2,x) ->
                                   let uu____6949 =
                                     let uu____6952 =
                                       let uu____6955 =
                                         let uu____6956 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____6956
                                          in
                                       [uu____6955]  in
                                     FStar_List.append typs uu____6952  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___128_6982 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___128_6982.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___128_6982.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6949)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6789 with
             | (env1,uu____7010,targs) ->
                 let uu____7032 =
                   let uu____7037 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7037
                    in
                 (match uu____7032 with
                  | (tup,uu____7047) ->
                      let uu____7048 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7048, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7073 = uncurry binders t  in
            (match uu____7073 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___94_7115 =
                   match uu___94_7115 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7129 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7129
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7151 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7151 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7160 = aux env [] bs  in (uu____7160, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7181 = desugar_binder env b  in
            (match uu____7181 with
             | (FStar_Pervasives_Native.None ,uu____7192) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7206 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____7206 with
                  | ((x,uu____7216),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____7223 =
                        let uu____7226 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____7226  in
                      (uu____7223, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____7258 =
              FStar_List.fold_left
                (fun uu____7278  ->
                   fun pat  ->
                     match uu____7278 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____7304,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____7314 =
                                let uu____7317 = free_type_vars env1 t  in
                                FStar_List.append uu____7317 ftvs  in
                              (env1, uu____7314)
                          | FStar_Parser_AST.PatAscribed
                              (uu____7322,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____7333 =
                                let uu____7336 = free_type_vars env1 t  in
                                let uu____7339 =
                                  let uu____7342 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____7342 ftvs  in
                                FStar_List.append uu____7336 uu____7339  in
                              (env1, uu____7333)
                          | uu____7347 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____7258 with
             | (uu____7356,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____7368 =
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
                   FStar_List.append uu____7368 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___95_7421 =
                   match uu___95_7421 with
                   | [] ->
                       let uu____7444 = desugar_term_aq env1 body  in
                       (match uu____7444 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7475 =
                                      let uu____7476 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7476
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7475 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7529 =
                              let uu____7532 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7532  in
                            (uu____7529, aq))
                   | p::rest ->
                       let uu____7545 = desugar_binding_pat env1 p  in
                       (match uu____7545 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7573 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7578 =
                              match b with
                              | LetBinder uu____7611 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7667) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7703 =
                                          let uu____7708 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7708, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7703
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7744,uu____7745) ->
                                             let tup2 =
                                               let uu____7747 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7747
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7751 =
                                                 let uu____7758 =
                                                   let uu____7759 =
                                                     let uu____7774 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7777 =
                                                       let uu____7780 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7781 =
                                                         let uu____7784 =
                                                           let uu____7785 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7785
                                                            in
                                                         [uu____7784]  in
                                                       uu____7780 ::
                                                         uu____7781
                                                        in
                                                     (uu____7774, uu____7777)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7759
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7758
                                                  in
                                               uu____7751
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____7796 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7796
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____7827,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____7829,pats)) ->
                                             let tupn =
                                               let uu____7868 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7868
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7878 =
                                                 let uu____7879 =
                                                   let uu____7894 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____7897 =
                                                     let uu____7906 =
                                                       let uu____7915 =
                                                         let uu____7916 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7916
                                                          in
                                                       [uu____7915]  in
                                                     FStar_List.append args
                                                       uu____7906
                                                      in
                                                   (uu____7894, uu____7897)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____7879
                                                  in
                                               mk1 uu____7878  in
                                             let p2 =
                                               let uu____7936 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____7936
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____7971 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7578 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____8042,uu____8043,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____8065 =
                let uu____8066 = unparen e  in uu____8066.FStar_Parser_AST.tm
                 in
              match uu____8065 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____8076 ->
                  let uu____8077 = desugar_term_aq env e  in
                  (match uu____8077 with
                   | (head1,aq) ->
                       let uu____8090 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____8090, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____8097 ->
            let rec aux args aqs e =
              let uu____8156 =
                let uu____8157 = unparen e  in uu____8157.FStar_Parser_AST.tm
                 in
              match uu____8156 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____8177 = desugar_term_aq env t  in
                  (match uu____8177 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____8213 ->
                  let uu____8214 = desugar_term_aq env e  in
                  (match uu____8214 with
                   | (head1,aq) ->
                       let uu____8237 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____8237, (join_aqs (aq :: aqs))))
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
            let uu____8277 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____8277
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
            let uu____8329 = desugar_term_aq env t  in
            (match uu____8329 with
             | (tm,s) ->
                 let uu____8340 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____8340, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____8348 =
              let uu____8361 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____8361 then desugar_typ_aq else desugar_term_aq  in
            uu____8348 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8416 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8559  ->
                        match uu____8559 with
                        | (attr_opt,(p,def)) ->
                            let uu____8617 = is_app_pattern p  in
                            if uu____8617
                            then
                              let uu____8648 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8648, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____8730 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____8730, def1)
                               | uu____8775 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____8813);
                                           FStar_Parser_AST.prange =
                                             uu____8814;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____8862 =
                                            let uu____8883 =
                                              let uu____8888 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8888  in
                                            (uu____8883, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____8862, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____8979) ->
                                        if top_level
                                        then
                                          let uu____9014 =
                                            let uu____9035 =
                                              let uu____9040 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9040  in
                                            (uu____9035, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____9014, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____9130 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____9161 =
                FStar_List.fold_left
                  (fun uu____9234  ->
                     fun uu____9235  ->
                       match (uu____9234, uu____9235) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____9343,uu____9344),uu____9345))
                           ->
                           let uu____9462 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9488 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9488 with
                                  | (env2,xx) ->
                                      let uu____9507 =
                                        let uu____9510 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9510 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9507))
                             | FStar_Util.Inr l ->
                                 let uu____9518 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____9518, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9462 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____9161 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9666 =
                    match uu____9666 with
                    | (attrs_opt,(uu____9702,args,result_t),def) ->
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
                                let uu____9790 = is_comp_type env1 t  in
                                if uu____9790
                                then
                                  ((let uu____9792 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____9802 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____9802))
                                       in
                                    match uu____9792 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____9805 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____9807 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____9807))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____9805
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____9811 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____9811 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____9815 ->
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
                              let uu____9830 =
                                let uu____9831 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____9831
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____9830
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
                  let uu____9890 = desugar_term_aq env' body  in
                  (match uu____9890 with
                   | (body1,aq) ->
                       let uu____9903 =
                         let uu____9906 =
                           let uu____9907 =
                             let uu____9920 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____9920)  in
                           FStar_Syntax_Syntax.Tm_let uu____9907  in
                         FStar_All.pipe_left mk1 uu____9906  in
                       (uu____9903, aq))
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
              let uu____9988 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____9988 with
              | (env1,binder,pat1) ->
                  let uu____10010 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____10036 = desugar_term_aq env1 t2  in
                        (match uu____10036 with
                         | (body1,aq) ->
                             let fv =
                               let uu____10050 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____10050
                                 FStar_Pervasives_Native.None
                                in
                             let uu____10051 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____10051, aq))
                    | LocalBinder (x,uu____10075) ->
                        let uu____10076 = desugar_term_aq env1 t2  in
                        (match uu____10076 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____10090;
                                   FStar_Syntax_Syntax.p = uu____10091;_}::[]
                                   -> body1
                               | uu____10096 ->
                                   let uu____10099 =
                                     let uu____10106 =
                                       let uu____10107 =
                                         let uu____10130 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____10131 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____10130, uu____10131)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____10107
                                        in
                                     FStar_Syntax_Syntax.mk uu____10106  in
                                   uu____10099 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____10141 =
                               let uu____10144 =
                                 let uu____10145 =
                                   let uu____10158 =
                                     let uu____10159 =
                                       let uu____10160 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____10160]  in
                                     FStar_Syntax_Subst.close uu____10159
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____10158)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____10145  in
                               FStar_All.pipe_left mk1 uu____10144  in
                             (uu____10141, aq))
                     in
                  (match uu____10010 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____10201 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____10201, aq)
                       else (tm, aq))
               in
            let uu____10213 = FStar_List.hd lbs  in
            (match uu____10213 with
             | (attrs,(head_pat,defn)) ->
                 let uu____10257 = is_rec || (is_app_pattern head_pat)  in
                 if uu____10257
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____10270 =
                let uu____10271 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____10271  in
              mk1 uu____10270  in
            let uu____10272 = desugar_term_aq env t1  in
            (match uu____10272 with
             | (t1',aq1) ->
                 let uu____10283 = desugar_term_aq env t2  in
                 (match uu____10283 with
                  | (t2',aq2) ->
                      let uu____10294 = desugar_term_aq env t3  in
                      (match uu____10294 with
                       | (t3',aq3) ->
                           let uu____10305 =
                             let uu____10308 =
                               let uu____10309 =
                                 let uu____10332 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None)
                                    in
                                 let uu____10353 =
                                   let uu____10368 =
                                     let uu____10381 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____10381,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____10392 =
                                     let uu____10407 =
                                       let uu____10420 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____10420,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____10407]  in
                                   uu____10368 :: uu____10392  in
                                 (uu____10332, uu____10353)  in
                               FStar_Syntax_Syntax.Tm_match uu____10309  in
                             mk1 uu____10308  in
                           (uu____10305, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10581 =
              match uu____10581 with
              | (pat,wopt,b) ->
                  let uu____10603 = desugar_match_pat env pat  in
                  (match uu____10603 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____10628 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____10628
                          in
                       let uu____10629 = desugar_term_aq env1 b  in
                       (match uu____10629 with
                        | (b1,aq) ->
                            let uu____10642 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____10642, aq)))
               in
            let uu____10647 = desugar_term_aq env e  in
            (match uu____10647 with
             | (e1,aq) ->
                 let uu____10658 =
                   let uu____10667 =
                     let uu____10678 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____10678 FStar_List.unzip  in
                   FStar_All.pipe_right uu____10667
                     (fun uu____10742  ->
                        match uu____10742 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____10658 with
                  | (brs,aqs) ->
                      let uu____10793 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____10793, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____10826 = is_comp_type env t  in
              if uu____10826
              then
                let uu____10833 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____10833
              else
                (let uu____10839 = desugar_term env t  in
                 FStar_Util.Inl uu____10839)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____10845 = desugar_term_aq env e  in
            (match uu____10845 with
             | (e1,aq) ->
                 let uu____10856 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____10856, aq))
        | FStar_Parser_AST.Record (uu____10885,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____10926 = FStar_List.hd fields  in
              match uu____10926 with | (f,uu____10938) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____10984  ->
                        match uu____10984 with
                        | (g,uu____10990) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____10996,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____11010 =
                         let uu____11015 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____11015)
                          in
                       FStar_Errors.raise_error uu____11010
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
                  let uu____11023 =
                    let uu____11034 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____11065  ->
                              match uu____11065 with
                              | (f,uu____11075) ->
                                  let uu____11076 =
                                    let uu____11077 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____11077
                                     in
                                  (uu____11076, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____11034)  in
                  FStar_Parser_AST.Construct uu____11023
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____11095 =
                      let uu____11096 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____11096  in
                    FStar_Parser_AST.mk_term uu____11095
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____11098 =
                      let uu____11111 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____11141  ->
                                match uu____11141 with
                                | (f,uu____11151) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____11111)  in
                    FStar_Parser_AST.Record uu____11098  in
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
            let uu____11211 = desugar_term_aq env recterm1  in
            (match uu____11211 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____11227;
                         FStar_Syntax_Syntax.vars = uu____11228;_},args)
                      ->
                      let uu____11250 =
                        let uu____11253 =
                          let uu____11254 =
                            let uu____11269 =
                              let uu____11270 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____11271 =
                                let uu____11274 =
                                  let uu____11275 =
                                    let uu____11282 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____11282)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____11275
                                   in
                                FStar_Pervasives_Native.Some uu____11274  in
                              FStar_Syntax_Syntax.fvar uu____11270
                                FStar_Syntax_Syntax.Delta_constant
                                uu____11271
                               in
                            (uu____11269, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____11254  in
                        FStar_All.pipe_left mk1 uu____11253  in
                      (uu____11250, s)
                  | uu____11311 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____11315 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____11315 with
              | (constrname,is_rec) ->
                  let uu____11330 = desugar_term_aq env e  in
                  (match uu____11330 with
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
                       let uu____11348 =
                         let uu____11351 =
                           let uu____11352 =
                             let uu____11367 =
                               let uu____11368 =
                                 let uu____11369 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____11369
                                  in
                               FStar_Syntax_Syntax.fvar uu____11368
                                 FStar_Syntax_Syntax.Delta_equational qual
                                in
                             let uu____11370 =
                               let uu____11373 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____11373]  in
                             (uu____11367, uu____11370)  in
                           FStar_Syntax_Syntax.Tm_app uu____11352  in
                         FStar_All.pipe_left mk1 uu____11351  in
                       (uu____11348, s))))
        | FStar_Parser_AST.NamedTyp (uu____11380,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____11389 =
              let uu____11390 = FStar_Syntax_Subst.compress tm  in
              uu____11390.FStar_Syntax_Syntax.n  in
            (match uu____11389 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____11398 =
                   let uu___129_11401 =
                     let uu____11402 =
                       let uu____11403 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____11403  in
                     FStar_Syntax_Util.exp_string uu____11402  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___129_11401.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___129_11401.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____11398, noaqs)
             | uu____11416 ->
                 let uu____11417 =
                   let uu____11422 =
                     let uu____11423 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____11423
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____11422)  in
                 FStar_Errors.raise_error uu____11417
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____11429 = desugar_term_aq env e  in
            (match uu____11429 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____11441 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____11441, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____11461 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____11462 =
              let uu____11471 =
                let uu____11478 = desugar_term env e  in (bv, b, uu____11478)
                 in
              [uu____11471]  in
            (uu____11461, uu____11462)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____11509 =
              let uu____11512 =
                let uu____11513 =
                  let uu____11520 = desugar_term env e  in (uu____11520, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____11513  in
              FStar_All.pipe_left mk1 uu____11512  in
            (uu____11509, noaqs)
        | uu____11535 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____11536 = desugar_formula env top  in
            (uu____11536, noaqs)
        | uu____11547 ->
            let uu____11548 =
              let uu____11553 =
                let uu____11554 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____11554  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____11553)  in
            FStar_Errors.raise_error uu____11548 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____11560 -> false
    | uu____11569 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____11575 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____11575 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____11579 -> false

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
           (fun uu____11616  ->
              match uu____11616 with
              | (a,imp) ->
                  let uu____11629 = desugar_term env a  in
                  arg_withimp_e imp uu____11629))

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
        let is_requires uu____11661 =
          match uu____11661 with
          | (t1,uu____11667) ->
              let uu____11668 =
                let uu____11669 = unparen t1  in
                uu____11669.FStar_Parser_AST.tm  in
              (match uu____11668 with
               | FStar_Parser_AST.Requires uu____11670 -> true
               | uu____11677 -> false)
           in
        let is_ensures uu____11687 =
          match uu____11687 with
          | (t1,uu____11693) ->
              let uu____11694 =
                let uu____11695 = unparen t1  in
                uu____11695.FStar_Parser_AST.tm  in
              (match uu____11694 with
               | FStar_Parser_AST.Ensures uu____11696 -> true
               | uu____11703 -> false)
           in
        let is_app head1 uu____11718 =
          match uu____11718 with
          | (t1,uu____11724) ->
              let uu____11725 =
                let uu____11726 = unparen t1  in
                uu____11726.FStar_Parser_AST.tm  in
              (match uu____11725 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____11728;
                      FStar_Parser_AST.level = uu____11729;_},uu____11730,uu____11731)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____11732 -> false)
           in
        let is_smt_pat uu____11742 =
          match uu____11742 with
          | (t1,uu____11748) ->
              let uu____11749 =
                let uu____11750 = unparen t1  in
                uu____11750.FStar_Parser_AST.tm  in
              (match uu____11749 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____11753);
                             FStar_Parser_AST.range = uu____11754;
                             FStar_Parser_AST.level = uu____11755;_},uu____11756)::uu____11757::[])
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
                             FStar_Parser_AST.range = uu____11796;
                             FStar_Parser_AST.level = uu____11797;_},uu____11798)::uu____11799::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____11824 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____11856 = head_and_args t1  in
          match uu____11856 with
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
                   let thunk_ens uu____11954 =
                     match uu____11954 with
                     | (e,i) ->
                         let uu____11965 = thunk_ens_ e  in (uu____11965, i)
                      in
                   let fail_lemma uu____11977 =
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
                         let uu____12057 =
                           let uu____12064 =
                             let uu____12071 = thunk_ens ens  in
                             [uu____12071; nil_pat]  in
                           req_true :: uu____12064  in
                         unit_tm :: uu____12057
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____12118 =
                           let uu____12125 =
                             let uu____12132 = thunk_ens ens  in
                             [uu____12132; nil_pat]  in
                           req :: uu____12125  in
                         unit_tm :: uu____12118
                     | ens::smtpat::[] when
                         (((let uu____12181 = is_requires ens  in
                            Prims.op_Negation uu____12181) &&
                             (let uu____12183 = is_smt_pat ens  in
                              Prims.op_Negation uu____12183))
                            &&
                            (let uu____12185 = is_decreases ens  in
                             Prims.op_Negation uu____12185))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____12186 =
                           let uu____12193 =
                             let uu____12200 = thunk_ens ens  in
                             [uu____12200; smtpat]  in
                           req_true :: uu____12193  in
                         unit_tm :: uu____12186
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____12247 =
                           let uu____12254 =
                             let uu____12261 = thunk_ens ens  in
                             [uu____12261; nil_pat; dec]  in
                           req_true :: uu____12254  in
                         unit_tm :: uu____12247
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12321 =
                           let uu____12328 =
                             let uu____12335 = thunk_ens ens  in
                             [uu____12335; smtpat; dec]  in
                           req_true :: uu____12328  in
                         unit_tm :: uu____12321
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____12395 =
                           let uu____12402 =
                             let uu____12409 = thunk_ens ens  in
                             [uu____12409; nil_pat; dec]  in
                           req :: uu____12402  in
                         unit_tm :: uu____12395
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12469 =
                           let uu____12476 =
                             let uu____12483 = thunk_ens ens  in
                             [uu____12483; smtpat]  in
                           req :: uu____12476  in
                         unit_tm :: uu____12469
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____12548 =
                           let uu____12555 =
                             let uu____12562 = thunk_ens ens  in
                             [uu____12562; dec; smtpat]  in
                           req :: uu____12555  in
                         unit_tm :: uu____12548
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____12624 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____12624, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12652 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12652
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____12653 =
                     let uu____12660 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12660, [])  in
                   (uu____12653, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12678 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12678
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____12679 =
                     let uu____12686 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12686, [])  in
                   (uu____12679, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____12702 =
                     let uu____12709 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12709, [])  in
                   (uu____12702, [(t1, FStar_Parser_AST.Nothing)])
               | uu____12732 ->
                   let default_effect =
                     let uu____12734 = FStar_Options.ml_ish ()  in
                     if uu____12734
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____12737 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____12737
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____12739 =
                     let uu____12746 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12746, [])  in
                   (uu____12739, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____12769 = pre_process_comp_typ t  in
        match uu____12769 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____12818 =
                  let uu____12823 =
                    let uu____12824 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____12824
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____12823)  in
                fail1 uu____12818)
             else ();
             (let is_universe uu____12835 =
                match uu____12835 with
                | (uu____12840,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____12842 = FStar_Util.take is_universe args  in
              match uu____12842 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____12901  ->
                         match uu____12901 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____12908 =
                    let uu____12923 = FStar_List.hd args1  in
                    let uu____12932 = FStar_List.tl args1  in
                    (uu____12923, uu____12932)  in
                  (match uu____12908 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____12987 =
                         let is_decrease uu____13025 =
                           match uu____13025 with
                           | (t1,uu____13035) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____13045;
                                       FStar_Syntax_Syntax.vars = uu____13046;_},uu____13047::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____13078 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____12987 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____13192  ->
                                      match uu____13192 with
                                      | (t1,uu____13202) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____13211,(arg,uu____13213)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____13242 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____13259 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____13270 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____13270
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____13274 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____13274
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____13281 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____13281
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____13285 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____13285
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____13289 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____13289
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____13293 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____13293
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____13311 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____13311
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
                                                  let uu____13400 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____13400
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
                                            | uu____13415 -> pat  in
                                          let uu____13416 =
                                            let uu____13427 =
                                              let uu____13438 =
                                                let uu____13447 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____13447, aq)  in
                                              [uu____13438]  in
                                            ens :: uu____13427  in
                                          req :: uu____13416
                                      | uu____13488 -> rest2
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
        | uu____13512 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___130_13533 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___130_13533.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___130_13533.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___131_13575 = b  in
             {
               FStar_Parser_AST.b = (uu___131_13575.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___131_13575.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___131_13575.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____13638 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____13638)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____13651 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____13651 with
             | (env1,a1) ->
                 let a2 =
                   let uu___132_13661 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___132_13661.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___132_13661.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____13683 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____13697 =
                     let uu____13700 =
                       let uu____13701 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____13701]  in
                     no_annot_abs uu____13700 body2  in
                   FStar_All.pipe_left setpos uu____13697  in
                 let uu____13706 =
                   let uu____13707 =
                     let uu____13722 =
                       let uu____13723 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____13723
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____13724 =
                       let uu____13727 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____13727]  in
                     (uu____13722, uu____13724)  in
                   FStar_Syntax_Syntax.Tm_app uu____13707  in
                 FStar_All.pipe_left mk1 uu____13706)
        | uu____13732 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____13812 = q (rest, pats, body)  in
              let uu____13819 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____13812 uu____13819
                FStar_Parser_AST.Formula
               in
            let uu____13820 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____13820 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____13829 -> failwith "impossible"  in
      let uu____13832 =
        let uu____13833 = unparen f  in uu____13833.FStar_Parser_AST.tm  in
      match uu____13832 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____13840,uu____13841) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____13852,uu____13853) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13884 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____13884
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13920 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____13920
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____13963 -> desugar_term env f

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
      let uu____13968 =
        FStar_List.fold_left
          (fun uu____14004  ->
             fun b  ->
               match uu____14004 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___133_14056 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___133_14056.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___133_14056.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___133_14056.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____14073 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____14073 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___134_14093 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___134_14093.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___134_14093.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____14110 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____13968 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____14197 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14197)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____14202 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14202)
      | FStar_Parser_AST.TVariable x ->
          let uu____14206 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____14206)
      | FStar_Parser_AST.NoName t ->
          let uu____14214 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____14214)
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
               (fun uu___96_14253  ->
                  match uu___96_14253 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____14254 -> false))
           in
        let quals2 q =
          let uu____14267 =
            (let uu____14270 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____14270) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____14267
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____14284 = FStar_Ident.range_of_lid disc_name  in
                let uu____14285 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____14284;
                  FStar_Syntax_Syntax.sigquals = uu____14285;
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
            let uu____14326 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____14356  ->
                        match uu____14356 with
                        | (x,uu____14364) ->
                            let uu____14365 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____14365 with
                             | (field_name,uu____14373) ->
                                 let only_decl =
                                   ((let uu____14377 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____14377)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____14379 =
                                        let uu____14380 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____14380.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____14379)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____14396 =
                                       FStar_List.filter
                                         (fun uu___97_14400  ->
                                            match uu___97_14400 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____14401 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____14396
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___98_14414  ->
                                             match uu___98_14414 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____14415 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____14417 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____14417;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____14424 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____14424
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____14429 =
                                        let uu____14434 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____14434  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____14429;
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
                                      let uu____14438 =
                                        let uu____14439 =
                                          let uu____14446 =
                                            let uu____14449 =
                                              let uu____14450 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____14450
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____14449]  in
                                          ((false, [lb]), uu____14446)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____14439
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____14438;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____14326 FStar_List.flatten
  
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
            (lid,uu____14500,t,uu____14502,n1,uu____14504) when
            let uu____14509 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____14509 ->
            let uu____14510 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____14510 with
             | (formals,uu____14526) ->
                 (match formals with
                  | [] -> []
                  | uu____14549 ->
                      let filter_records uu___99_14563 =
                        match uu___99_14563 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____14566,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____14578 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____14580 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____14580 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____14590 = FStar_Util.first_N n1 formals  in
                      (match uu____14590 with
                       | (uu____14613,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____14639 -> []
  
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
                    let uu____14705 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____14705
                    then
                      let uu____14708 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____14708
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____14711 =
                      let uu____14716 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____14716  in
                    let uu____14717 =
                      let uu____14720 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____14720  in
                    let uu____14723 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____14711;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____14717;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____14723;
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
          let tycon_id uu___100_14780 =
            match uu___100_14780 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____14782,uu____14783) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____14793,uu____14794,uu____14795) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____14805,uu____14806,uu____14807) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____14837,uu____14838,uu____14839) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____14883) ->
                let uu____14884 =
                  let uu____14885 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14885  in
                FStar_Parser_AST.mk_term uu____14884 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____14887 =
                  let uu____14888 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14888  in
                FStar_Parser_AST.mk_term uu____14887 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____14890) ->
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
              | uu____14921 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____14927 =
                     let uu____14928 =
                       let uu____14935 = binder_to_term b  in
                       (out, uu____14935, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____14928  in
                   FStar_Parser_AST.mk_term uu____14927
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___101_14947 =
            match uu___101_14947 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____15003  ->
                       match uu____15003 with
                       | (x,t,uu____15014) ->
                           let uu____15019 =
                             let uu____15020 =
                               let uu____15025 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____15025, t)  in
                             FStar_Parser_AST.Annotated uu____15020  in
                           FStar_Parser_AST.mk_binder uu____15019
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____15027 =
                    let uu____15028 =
                      let uu____15029 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____15029  in
                    FStar_Parser_AST.mk_term uu____15028
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____15027 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____15033 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____15060  ->
                          match uu____15060 with
                          | (x,uu____15070,uu____15071) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____15033)
            | uu____15124 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___102_15163 =
            match uu___102_15163 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____15187 = typars_of_binders _env binders  in
                (match uu____15187 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____15229 =
                         let uu____15230 =
                           let uu____15231 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____15231  in
                         FStar_Parser_AST.mk_term uu____15230
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____15229 binders  in
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
            | uu____15244 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____15292 =
              FStar_List.fold_left
                (fun uu____15332  ->
                   fun uu____15333  ->
                     match (uu____15332, uu____15333) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____15424 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____15424 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____15292 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____15537 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____15537
                | uu____15538 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____15546 = desugar_abstract_tc quals env [] tc  in
              (match uu____15546 with
               | (uu____15559,uu____15560,se,uu____15562) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____15565,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____15582 =
                                 let uu____15583 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____15583  in
                               if uu____15582
                               then
                                 let uu____15584 =
                                   let uu____15589 =
                                     let uu____15590 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____15590
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____15589)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____15584
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
                           | uu____15597 ->
                               let uu____15598 =
                                 let uu____15605 =
                                   let uu____15606 =
                                     let uu____15619 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____15619)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____15606
                                    in
                                 FStar_Syntax_Syntax.mk uu____15605  in
                               uu____15598 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___135_15623 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___135_15623.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___135_15623.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___135_15623.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____15626 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____15629 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____15629
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____15644 = typars_of_binders env binders  in
              (match uu____15644 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15680 =
                           FStar_Util.for_some
                             (fun uu___103_15682  ->
                                match uu___103_15682 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____15683 -> false) quals
                            in
                         if uu____15680
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____15690 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___104_15694  ->
                               match uu___104_15694 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____15695 -> false))
                        in
                     if uu____15690
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____15704 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____15704
                     then
                       let uu____15707 =
                         let uu____15714 =
                           let uu____15715 = unparen t  in
                           uu____15715.FStar_Parser_AST.tm  in
                         match uu____15714 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____15736 =
                               match FStar_List.rev args with
                               | (last_arg,uu____15766)::args_rev ->
                                   let uu____15778 =
                                     let uu____15779 = unparen last_arg  in
                                     uu____15779.FStar_Parser_AST.tm  in
                                   (match uu____15778 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____15807 -> ([], args))
                               | uu____15816 -> ([], args)  in
                             (match uu____15736 with
                              | (cattributes,args1) ->
                                  let uu____15855 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____15855))
                         | uu____15866 -> (t, [])  in
                       match uu____15707 with
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
                                  (fun uu___105_15888  ->
                                     match uu___105_15888 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____15889 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____15900)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____15924 = tycon_record_as_variant trec  in
              (match uu____15924 with
               | (t,fs) ->
                   let uu____15941 =
                     let uu____15944 =
                       let uu____15945 =
                         let uu____15954 =
                           let uu____15957 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____15957  in
                         (uu____15954, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____15945  in
                     uu____15944 :: quals  in
                   desugar_tycon env d uu____15941 [t])
          | uu____15962::uu____15963 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____16130 = et  in
                match uu____16130 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____16355 ->
                         let trec = tc  in
                         let uu____16379 = tycon_record_as_variant trec  in
                         (match uu____16379 with
                          | (t,fs) ->
                              let uu____16438 =
                                let uu____16441 =
                                  let uu____16442 =
                                    let uu____16451 =
                                      let uu____16454 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____16454  in
                                    (uu____16451, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____16442
                                   in
                                uu____16441 :: quals1  in
                              collect_tcs uu____16438 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____16541 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16541 with
                          | (env2,uu____16601,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____16750 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16750 with
                          | (env2,uu____16810,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____16935 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____16982 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____16982 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___107_17493  ->
                             match uu___107_17493 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____17560,uu____17561);
                                    FStar_Syntax_Syntax.sigrng = uu____17562;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____17563;
                                    FStar_Syntax_Syntax.sigmeta = uu____17564;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17565;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____17626 =
                                     typars_of_binders env1 binders  in
                                   match uu____17626 with
                                   | (env2,tpars1) ->
                                       let uu____17657 =
                                         push_tparams env2 tpars1  in
                                       (match uu____17657 with
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
                                 let uu____17690 =
                                   let uu____17711 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____17711)
                                    in
                                 [uu____17690]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____17779);
                                    FStar_Syntax_Syntax.sigrng = uu____17780;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____17782;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17783;_},constrs,tconstr,quals1)
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
                                 let uu____17881 = push_tparams env1 tpars
                                    in
                                 (match uu____17881 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____17958  ->
                                             match uu____17958 with
                                             | (x,uu____17972) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____17980 =
                                        let uu____18009 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____18123  ->
                                                  match uu____18123 with
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
                                                        let uu____18179 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____18179
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
                                                                uu___106_18190
                                                                 ->
                                                                match uu___106_18190
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____18202
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____18210 =
                                                        let uu____18231 =
                                                          let uu____18232 =
                                                            let uu____18233 =
                                                              let uu____18248
                                                                =
                                                                let uu____18251
                                                                  =
                                                                  let uu____18254
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____18254
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____18251
                                                                 in
                                                              (name, univs1,
                                                                uu____18248,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____18233
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____18232;
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
                                                          uu____18231)
                                                         in
                                                      (name, uu____18210)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____18009
                                         in
                                      (match uu____17980 with
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
                             | uu____18493 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18625  ->
                             match uu____18625 with
                             | (name_doc,uu____18653,uu____18654) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18734  ->
                             match uu____18734 with
                             | (uu____18755,uu____18756,se) -> se))
                      in
                   let uu____18786 =
                     let uu____18793 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____18793 rng
                      in
                   (match uu____18786 with
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
                               (fun uu____18859  ->
                                  match uu____18859 with
                                  | (uu____18882,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____18933,tps,k,uu____18936,constrs)
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
                                  | uu____18955 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____18972  ->
                                 match uu____18972 with
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
      let uu____19011 =
        FStar_List.fold_left
          (fun uu____19034  ->
             fun b  ->
               match uu____19034 with
               | (env1,binders1) ->
                   let uu____19054 = desugar_binder env1 b  in
                   (match uu____19054 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19071 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____19071 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____19088 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____19011 with
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
          let uu____19141 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___108_19146  ->
                    match uu___108_19146 with
                    | FStar_Syntax_Syntax.Reflectable uu____19147 -> true
                    | uu____19148 -> false))
             in
          if uu____19141
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____19151 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____19151
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
                  let uu____19295 = desugar_binders monad_env eff_binders  in
                  match uu____19295 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____19316 =
                          let uu____19317 =
                            let uu____19324 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____19324  in
                          FStar_List.length uu____19317  in
                        uu____19316 = (Prims.parse_int "1")  in
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
                            (uu____19368,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____19370,uu____19371,uu____19372),uu____19373)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____19406 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____19407 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____19419 = name_of_eff_decl decl  in
                             FStar_List.mem uu____19419 mandatory_members)
                          eff_decls
                         in
                      (match uu____19407 with
                       | (mandatory_members_decls,actions) ->
                           let uu____19436 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____19465  ->
                                     fun decl  ->
                                       match uu____19465 with
                                       | (env2,out) ->
                                           let uu____19485 =
                                             desugar_decl env2 decl  in
                                           (match uu____19485 with
                                            | (env3,ses) ->
                                                let uu____19498 =
                                                  let uu____19501 =
                                                    FStar_List.hd ses  in
                                                  uu____19501 :: out  in
                                                (env3, uu____19498)))
                                  (env1, []))
                              in
                           (match uu____19436 with
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
                                              (uu____19569,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____19572,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____19573,
                                                                  (def,uu____19575)::
                                                                  (cps_type,uu____19577)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____19578;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____19579;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____19631 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19631 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19651 =
                                                     let uu____19652 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19653 =
                                                       let uu____19654 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19654
                                                        in
                                                     let uu____19659 =
                                                       let uu____19660 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19660
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19652;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19653;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____19659
                                                     }  in
                                                   (uu____19651, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____19667,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____19670,defn),doc1)::[])
                                              when for_free ->
                                              let uu____19705 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19705 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19725 =
                                                     let uu____19726 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19727 =
                                                       let uu____19728 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19728
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19726;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19727;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____19725, doc1))
                                          | uu____19735 ->
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
                                    let uu____19767 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____19767
                                     in
                                  let uu____19768 =
                                    let uu____19769 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____19769
                                     in
                                  ([], uu____19768)  in
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
                                      let uu____19786 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____19786)  in
                                    let uu____19793 =
                                      let uu____19794 =
                                        let uu____19795 =
                                          let uu____19796 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19796
                                           in
                                        let uu____19805 = lookup1 "return"
                                           in
                                        let uu____19806 = lookup1 "bind"  in
                                        let uu____19807 =
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
                                            uu____19795;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____19805;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____19806;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____19807
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____19794
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____19793;
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
                                         (fun uu___109_19813  ->
                                            match uu___109_19813 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____19814 -> true
                                            | uu____19815 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____19825 =
                                       let uu____19826 =
                                         let uu____19827 =
                                           lookup1 "return_wp"  in
                                         let uu____19828 = lookup1 "bind_wp"
                                            in
                                         let uu____19829 =
                                           lookup1 "if_then_else"  in
                                         let uu____19830 = lookup1 "ite_wp"
                                            in
                                         let uu____19831 = lookup1 "stronger"
                                            in
                                         let uu____19832 = lookup1 "close_wp"
                                            in
                                         let uu____19833 = lookup1 "assert_p"
                                            in
                                         let uu____19834 = lookup1 "assume_p"
                                            in
                                         let uu____19835 = lookup1 "null_wp"
                                            in
                                         let uu____19836 = lookup1 "trivial"
                                            in
                                         let uu____19837 =
                                           if rr
                                           then
                                             let uu____19838 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____19838
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____19854 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____19856 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____19858 =
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
                                             uu____19827;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____19828;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____19829;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____19830;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____19831;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____19832;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____19833;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____19834;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____19835;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____19836;
                                           FStar_Syntax_Syntax.repr =
                                             uu____19837;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____19854;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____19856;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____19858
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____19826
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____19825;
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
                                          fun uu____19884  ->
                                            match uu____19884 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____19898 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____19898
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
                let uu____19922 = desugar_binders env1 eff_binders  in
                match uu____19922 with
                | (env2,binders) ->
                    let uu____19941 =
                      let uu____19960 = head_and_args defn  in
                      match uu____19960 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____20005 ->
                                let uu____20006 =
                                  let uu____20011 =
                                    let uu____20012 =
                                      let uu____20013 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____20013 " not found"
                                       in
                                    Prims.strcat "Effect " uu____20012  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____20011)
                                   in
                                FStar_Errors.raise_error uu____20006
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____20015 =
                            match FStar_List.rev args with
                            | (last_arg,uu____20045)::args_rev ->
                                let uu____20057 =
                                  let uu____20058 = unparen last_arg  in
                                  uu____20058.FStar_Parser_AST.tm  in
                                (match uu____20057 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____20086 -> ([], args))
                            | uu____20095 -> ([], args)  in
                          (match uu____20015 with
                           | (cattributes,args1) ->
                               let uu____20146 = desugar_args env2 args1  in
                               let uu____20155 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____20146, uu____20155))
                       in
                    (match uu____19941 with
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
                          (let uu____20211 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____20211 with
                           | (ed_binders,uu____20225,ed_binders_opening) ->
                               let sub1 uu____20238 =
                                 match uu____20238 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____20252 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____20252 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____20256 =
                                       let uu____20257 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____20257)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____20256
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____20262 =
                                   let uu____20263 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____20263
                                    in
                                 let uu____20274 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____20275 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____20276 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____20277 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____20278 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____20279 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____20280 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____20281 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____20282 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____20283 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____20284 =
                                   let uu____20285 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____20285
                                    in
                                 let uu____20296 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____20297 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____20298 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____20306 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____20307 =
                                          let uu____20308 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____20308
                                           in
                                        let uu____20319 =
                                          let uu____20320 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____20320
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____20306;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____20307;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____20319
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
                                     uu____20262;
                                   FStar_Syntax_Syntax.ret_wp = uu____20274;
                                   FStar_Syntax_Syntax.bind_wp = uu____20275;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____20276;
                                   FStar_Syntax_Syntax.ite_wp = uu____20277;
                                   FStar_Syntax_Syntax.stronger = uu____20278;
                                   FStar_Syntax_Syntax.close_wp = uu____20279;
                                   FStar_Syntax_Syntax.assert_p = uu____20280;
                                   FStar_Syntax_Syntax.assume_p = uu____20281;
                                   FStar_Syntax_Syntax.null_wp = uu____20282;
                                   FStar_Syntax_Syntax.trivial = uu____20283;
                                   FStar_Syntax_Syntax.repr = uu____20284;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____20296;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____20297;
                                   FStar_Syntax_Syntax.actions = uu____20298;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____20333 =
                                     let uu____20334 =
                                       let uu____20341 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____20341
                                        in
                                     FStar_List.length uu____20334  in
                                   uu____20333 = (Prims.parse_int "1")  in
                                 let uu____20370 =
                                   let uu____20373 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____20373 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____20370;
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
                                             let uu____20395 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____20395
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____20397 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____20397
                                 then
                                   let reflect_lid =
                                     let uu____20401 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____20401
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
    let uu____20413 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____20413 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____20464 ->
              let uu____20465 =
                let uu____20466 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____20466
                 in
              Prims.strcat "\n  " uu____20465
          | uu____20467 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____20480  ->
               match uu____20480 with
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
          let uu____20498 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____20498
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____20500 =
          let uu____20509 = FStar_Syntax_Syntax.as_arg arg  in [uu____20509]
           in
        FStar_Syntax_Util.mk_app fv uu____20500

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____20516 = desugar_decl_noattrs env d  in
      match uu____20516 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____20536 = mk_comment_attr d  in uu____20536 :: attrs1  in
          let uu____20541 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___136_20547 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___136_20547.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___136_20547.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___136_20547.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___136_20547.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____20541)

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
      | FStar_Parser_AST.Fsdoc uu____20577 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____20593 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____20593, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____20632  ->
                 match uu____20632 with | (x,uu____20640) -> x) tcs
             in
          let uu____20645 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____20645 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____20667;
                    FStar_Parser_AST.prange = uu____20668;_},uu____20669)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____20678;
                    FStar_Parser_AST.prange = uu____20679;_},uu____20680)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____20695;
                         FStar_Parser_AST.prange = uu____20696;_},uu____20697);
                    FStar_Parser_AST.prange = uu____20698;_},uu____20699)::[]
                   -> false
               | (p,uu____20727)::[] ->
                   let uu____20736 = is_app_pattern p  in
                   Prims.op_Negation uu____20736
               | uu____20737 -> false)
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
            let uu____20810 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____20810 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____20822 =
                     let uu____20823 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____20823.FStar_Syntax_Syntax.n  in
                   match uu____20822 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____20831) ->
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
                         | uu____20864::uu____20865 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____20868 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___110_20883  ->
                                     match uu___110_20883 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____20886;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20887;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20888;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20889;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20890;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20891;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20892;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20904;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20905;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20906;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20907;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20908;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20909;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____20923 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____20954  ->
                                   match uu____20954 with
                                   | (uu____20967,(uu____20968,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____20923
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____20992 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____20992
                         then
                           let uu____21001 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___137_21015 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___138_21017 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___138_21017.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___138_21017.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___137_21015.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___137_21015.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___137_21015.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___137_21015.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___137_21015.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___137_21015.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____21001)
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
                   | uu____21052 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____21058 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____21077 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____21058 with
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
                       let uu___139_21113 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___139_21113.FStar_Parser_AST.prange)
                       }
                   | uu____21120 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___140_21127 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___140_21127.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___140_21127.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___140_21127.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____21163 id1 =
                   match uu____21163 with
                   | (env1,ses) ->
                       let main =
                         let uu____21184 =
                           let uu____21185 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____21185  in
                         FStar_Parser_AST.mk_term uu____21184
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
                       let uu____21235 = desugar_decl env1 id_decl  in
                       (match uu____21235 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____21253 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____21253 FStar_Util.set_elements
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
            let uu____21284 = close_fun env t  in
            desugar_term env uu____21284  in
          let quals1 =
            let uu____21288 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____21288
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____21294 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____21294;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____21306 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____21306 with
           | (t,uu____21320) ->
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
            let uu____21354 =
              let uu____21361 = FStar_Syntax_Syntax.null_binder t  in
              [uu____21361]  in
            let uu____21362 =
              let uu____21365 =
                let uu____21366 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____21366  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____21365
               in
            FStar_Syntax_Util.arrow uu____21354 uu____21362  in
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
            let uu____21431 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____21431 with
            | FStar_Pervasives_Native.None  ->
                let uu____21434 =
                  let uu____21439 =
                    let uu____21440 =
                      let uu____21441 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____21441 " not found"  in
                    Prims.strcat "Effect name " uu____21440  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____21439)  in
                FStar_Errors.raise_error uu____21434
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____21445 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____21487 =
                  let uu____21496 =
                    let uu____21503 = desugar_term env t  in
                    ([], uu____21503)  in
                  FStar_Pervasives_Native.Some uu____21496  in
                (uu____21487, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____21536 =
                  let uu____21545 =
                    let uu____21552 = desugar_term env wp  in
                    ([], uu____21552)  in
                  FStar_Pervasives_Native.Some uu____21545  in
                let uu____21561 =
                  let uu____21570 =
                    let uu____21577 = desugar_term env t  in
                    ([], uu____21577)  in
                  FStar_Pervasives_Native.Some uu____21570  in
                (uu____21536, uu____21561)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____21603 =
                  let uu____21612 =
                    let uu____21619 = desugar_term env t  in
                    ([], uu____21619)  in
                  FStar_Pervasives_Native.Some uu____21612  in
                (FStar_Pervasives_Native.None, uu____21603)
             in
          (match uu____21445 with
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
            let uu____21699 =
              let uu____21700 =
                let uu____21707 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____21707, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____21700  in
            {
              FStar_Syntax_Syntax.sigel = uu____21699;
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
      let uu____21735 =
        FStar_List.fold_left
          (fun uu____21755  ->
             fun d  ->
               match uu____21755 with
               | (env1,sigelts) ->
                   let uu____21775 = desugar_decl env1 d  in
                   (match uu____21775 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____21735 with
      | (env1,sigelts) ->
          let rec forward acc uu___112_21820 =
            match uu___112_21820 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____21834,FStar_Syntax_Syntax.Sig_let uu____21835) ->
                     let uu____21848 =
                       let uu____21851 =
                         let uu___141_21852 = se2  in
                         let uu____21853 =
                           let uu____21856 =
                             FStar_List.filter
                               (fun uu___111_21870  ->
                                  match uu___111_21870 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____21874;
                                           FStar_Syntax_Syntax.vars =
                                             uu____21875;_},uu____21876);
                                      FStar_Syntax_Syntax.pos = uu____21877;
                                      FStar_Syntax_Syntax.vars = uu____21878;_}
                                      when
                                      let uu____21901 =
                                        let uu____21902 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____21902
                                         in
                                      uu____21901 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____21903 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____21856
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___141_21852.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___141_21852.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___141_21852.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___141_21852.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____21853
                         }  in
                       uu____21851 :: se1 :: acc  in
                     forward uu____21848 sigelts1
                 | uu____21908 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____21916 = forward [] sigelts  in (env1, uu____21916)
  
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
      let uu____21958 =
        let uu____21965 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____21982  ->
               match uu____21982 with
               | ({ FStar_Syntax_Syntax.ppname = uu____21991;
                    FStar_Syntax_Syntax.index = uu____21992;
                    FStar_Syntax_Syntax.sort = t;_},uu____21994)
                   ->
                   let uu____21997 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____21997) uu____21965
         in
      FStar_All.pipe_right bs uu____21958  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____22005 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____22022 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____22050 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____22071,uu____22072,bs,t,uu____22075,uu____22076)
                            ->
                            let uu____22085 = bs_univnames bs  in
                            let uu____22088 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____22085 uu____22088
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____22091,uu____22092,t,uu____22094,uu____22095,uu____22096)
                            -> FStar_Syntax_Free.univnames t
                        | uu____22101 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____22050 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___142_22111 = s  in
        let uu____22112 =
          let uu____22113 =
            let uu____22122 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____22140,bs,t,lids1,lids2) ->
                          let uu___143_22153 = se  in
                          let uu____22154 =
                            let uu____22155 =
                              let uu____22172 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____22173 =
                                let uu____22174 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____22174 t  in
                              (lid, uvs, uu____22172, uu____22173, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____22155
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____22154;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___143_22153.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___143_22153.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___143_22153.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___143_22153.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____22188,t,tlid,n1,lids1) ->
                          let uu___144_22197 = se  in
                          let uu____22198 =
                            let uu____22199 =
                              let uu____22214 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____22214, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____22199  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____22198;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___144_22197.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___144_22197.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___144_22197.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___144_22197.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____22219 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____22122, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____22113  in
        {
          FStar_Syntax_Syntax.sigel = uu____22112;
          FStar_Syntax_Syntax.sigrng =
            (uu___142_22111.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___142_22111.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___142_22111.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___142_22111.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22225,t) ->
        let uvs =
          let uu____22230 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____22230 FStar_Util.set_elements  in
        let uu___145_22237 = s  in
        let uu____22238 =
          let uu____22239 =
            let uu____22246 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____22246)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____22239  in
        {
          FStar_Syntax_Syntax.sigel = uu____22238;
          FStar_Syntax_Syntax.sigrng =
            (uu___145_22237.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___145_22237.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___145_22237.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___145_22237.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____22276 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____22279 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____22286) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____22315,(FStar_Util.Inl t,uu____22317),uu____22318)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____22365,(FStar_Util.Inr c,uu____22367),uu____22368)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____22415 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____22416,(FStar_Util.Inl t,uu____22418),uu____22419) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____22466,(FStar_Util.Inr c,uu____22468),uu____22469) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____22516 -> empty_set  in
          FStar_Util.set_union uu____22276 uu____22279  in
        let all_lb_univs =
          let uu____22520 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____22536 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____22536) empty_set)
             in
          FStar_All.pipe_right uu____22520 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___146_22546 = s  in
        let uu____22547 =
          let uu____22548 =
            let uu____22555 =
              let uu____22562 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___147_22574 = lb  in
                        let uu____22575 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____22578 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___147_22574.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____22575;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___147_22574.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____22578;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___147_22574.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___147_22574.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____22562)  in
            (uu____22555, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____22548  in
        {
          FStar_Syntax_Syntax.sigel = uu____22547;
          FStar_Syntax_Syntax.sigrng =
            (uu___146_22546.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___146_22546.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___146_22546.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___146_22546.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____22592,fml) ->
        let uvs =
          let uu____22597 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____22597 FStar_Util.set_elements  in
        let uu___148_22604 = s  in
        let uu____22605 =
          let uu____22606 =
            let uu____22613 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____22613)  in
          FStar_Syntax_Syntax.Sig_assume uu____22606  in
        {
          FStar_Syntax_Syntax.sigel = uu____22605;
          FStar_Syntax_Syntax.sigrng =
            (uu___148_22604.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___148_22604.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___148_22604.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___148_22604.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____22617,bs,c,flags1) ->
        let uvs =
          let uu____22628 =
            let uu____22631 = bs_univnames bs  in
            let uu____22634 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____22631 uu____22634  in
          FStar_All.pipe_right uu____22628 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___149_22644 = s  in
        let uu____22645 =
          let uu____22646 =
            let uu____22659 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____22660 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____22659, uu____22660, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____22646  in
        {
          FStar_Syntax_Syntax.sigel = uu____22645;
          FStar_Syntax_Syntax.sigrng =
            (uu___149_22644.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___149_22644.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___149_22644.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___149_22644.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____22665 -> s
  
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
          | (FStar_Pervasives_Native.None ,uu____22700) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____22704;
               FStar_Syntax_Syntax.exports = uu____22705;
               FStar_Syntax_Syntax.is_interface = uu____22706;_},FStar_Parser_AST.Module
             (current_lid,uu____22708)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____22716) ->
              let uu____22719 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____22719
           in
        let uu____22724 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____22760 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____22760, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____22777 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____22777, mname, decls, false)
           in
        match uu____22724 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____22807 = desugar_decls env2 decls  in
            (match uu____22807 with
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
          let uu____22876 =
            (FStar_Options.interactive ()) &&
              (let uu____22878 =
                 let uu____22879 =
                   let uu____22880 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____22880  in
                 FStar_Util.get_file_extension uu____22879  in
               FStar_List.mem uu____22878 ["fsti"; "fsi"])
             in
          if uu____22876 then as_interface m else m  in
        let uu____22884 = desugar_modul_common curmod env m1  in
        match uu____22884 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____22899 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____22919 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____22919 with
      | (env1,modul,pop_when_done) ->
          let uu____22933 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____22933 with
           | (env2,modul1) ->
               ((let uu____22945 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____22945
                 then
                   let uu____22946 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____22946
                 else ());
                (let uu____22948 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____22948, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____22966 = desugar_modul env modul  in
      match uu____22966 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____22997 = desugar_decls env decls  in
      match uu____22997 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____23041 = desugar_partial_modul modul env a_modul  in
        match uu____23041 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____23127 ->
                  let t =
                    let uu____23135 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____23135  in
                  let uu____23144 =
                    let uu____23145 = FStar_Syntax_Subst.compress t  in
                    uu____23145.FStar_Syntax_Syntax.n  in
                  (match uu____23144 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____23155,uu____23156)
                       -> bs1
                   | uu____23177 -> failwith "Impossible")
               in
            let uu____23184 =
              let uu____23191 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____23191
                FStar_Syntax_Syntax.t_unit
               in
            match uu____23184 with
            | (binders,uu____23193,binders_opening) ->
                let erase_term t =
                  let uu____23201 =
                    let uu____23202 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____23202  in
                  FStar_Syntax_Subst.close binders uu____23201  in
                let erase_tscheme uu____23220 =
                  match uu____23220 with
                  | (us,t) ->
                      let t1 =
                        let uu____23240 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____23240 t  in
                      let uu____23243 =
                        let uu____23244 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____23244  in
                      ([], uu____23243)
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
                    | uu____23275 ->
                        let bs =
                          let uu____23283 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____23283  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____23313 =
                          let uu____23314 =
                            let uu____23317 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____23317  in
                          uu____23314.FStar_Syntax_Syntax.n  in
                        (match uu____23313 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____23325,uu____23326) -> bs1
                         | uu____23347 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____23360 =
                      let uu____23361 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____23361  in
                    FStar_Syntax_Subst.close binders uu____23360  in
                  let uu___150_23362 = action  in
                  let uu____23363 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____23364 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___150_23362.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___150_23362.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____23363;
                    FStar_Syntax_Syntax.action_typ = uu____23364
                  }  in
                let uu___151_23365 = ed  in
                let uu____23366 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____23367 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____23368 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____23369 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____23370 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____23371 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____23372 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____23373 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____23374 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____23375 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____23376 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____23377 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____23378 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____23379 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____23380 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____23381 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___151_23365.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___151_23365.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____23366;
                  FStar_Syntax_Syntax.signature = uu____23367;
                  FStar_Syntax_Syntax.ret_wp = uu____23368;
                  FStar_Syntax_Syntax.bind_wp = uu____23369;
                  FStar_Syntax_Syntax.if_then_else = uu____23370;
                  FStar_Syntax_Syntax.ite_wp = uu____23371;
                  FStar_Syntax_Syntax.stronger = uu____23372;
                  FStar_Syntax_Syntax.close_wp = uu____23373;
                  FStar_Syntax_Syntax.assert_p = uu____23374;
                  FStar_Syntax_Syntax.assume_p = uu____23375;
                  FStar_Syntax_Syntax.null_wp = uu____23376;
                  FStar_Syntax_Syntax.trivial = uu____23377;
                  FStar_Syntax_Syntax.repr = uu____23378;
                  FStar_Syntax_Syntax.return_repr = uu____23379;
                  FStar_Syntax_Syntax.bind_repr = uu____23380;
                  FStar_Syntax_Syntax.actions = uu____23381;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___151_23365.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___152_23397 = se  in
                  let uu____23398 =
                    let uu____23399 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____23399  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____23398;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___152_23397.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___152_23397.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___152_23397.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___152_23397.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___153_23403 = se  in
                  let uu____23404 =
                    let uu____23405 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____23405
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____23404;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___153_23403.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___153_23403.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___153_23403.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___153_23403.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____23407 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____23408 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____23408 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____23420 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____23420
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____23422 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____23422)
  