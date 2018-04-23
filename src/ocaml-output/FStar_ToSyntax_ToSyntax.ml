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
      let uu____1896 =
        let uu____1911 =
          let uu____1914 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1914  in
        let uu____1915 =
          let uu____1924 =
            let uu____1931 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1931)  in
          [uu____1924]  in
        (uu____1911, uu____1915)  in
      FStar_Syntax_Syntax.Tm_app uu____1896  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1968 =
        let uu____1983 =
          let uu____1986 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1986  in
        let uu____1987 =
          let uu____1996 =
            let uu____2003 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2003)  in
          [uu____1996]  in
        (uu____1983, uu____1987)  in
      FStar_Syntax_Syntax.Tm_app uu____1968  in
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
          let uu____2054 =
            let uu____2069 =
              let uu____2072 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2072  in
            let uu____2073 =
              let uu____2082 =
                let uu____2089 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2089)  in
              let uu____2092 =
                let uu____2101 =
                  let uu____2108 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2108)  in
                [uu____2101]  in
              uu____2082 :: uu____2092  in
            (uu____2069, uu____2073)  in
          FStar_Syntax_Syntax.Tm_app uu____2054  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___90_2143  ->
    match uu___90_2143 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2144 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2156 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2156)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2175 =
      let uu____2176 = unparen t  in uu____2176.FStar_Parser_AST.tm  in
    match uu____2175 with
    | FStar_Parser_AST.Wild  ->
        let uu____2181 =
          let uu____2182 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2182  in
        FStar_Util.Inr uu____2181
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2193)) ->
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
             let uu____2258 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2258
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2269 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2269
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2280 =
               let uu____2285 =
                 let uu____2286 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2286
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2285)
                in
             FStar_Errors.raise_error uu____2280 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2291 ->
        let rec aux t1 univargs =
          let uu____2325 =
            let uu____2326 = unparen t1  in uu____2326.FStar_Parser_AST.tm
             in
          match uu____2325 with
          | FStar_Parser_AST.App (t2,targ,uu____2333) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___91_2356  ->
                     match uu___91_2356 with
                     | FStar_Util.Inr uu____2361 -> true
                     | uu____2362 -> false) univargs
              then
                let uu____2367 =
                  let uu____2368 =
                    FStar_List.map
                      (fun uu___92_2377  ->
                         match uu___92_2377 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2368  in
                FStar_Util.Inr uu____2367
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___93_2394  ->
                        match uu___93_2394 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2400 -> failwith "impossible")
                     univargs
                    in
                 let uu____2401 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2401)
          | uu____2407 ->
              let uu____2408 =
                let uu____2413 =
                  let uu____2414 =
                    let uu____2415 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2415 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2414  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2413)  in
              FStar_Errors.raise_error uu____2408 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2424 ->
        let uu____2425 =
          let uu____2430 =
            let uu____2431 =
              let uu____2432 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2432 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2431  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2430)  in
        FStar_Errors.raise_error uu____2425 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____2465 ->
        let uu____2488 =
          let uu____2493 =
            let uu____2494 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____2494
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____2493)  in
        FStar_Errors.raise_error uu____2488 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____2504 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2504) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2532 = FStar_List.hd fields  in
        match uu____2532 with
        | (f,uu____2542) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2554 =
                match uu____2554 with
                | (f',uu____2560) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2562 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____2562
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
              (let uu____2566 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2566);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2921 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2928 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2929 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2931,pats1) ->
                let aux out uu____2969 =
                  match uu____2969 with
                  | (p2,uu____2981) ->
                      let intersection =
                        let uu____2989 = pat_vars p2  in
                        FStar_Util.set_intersect uu____2989 out  in
                      let uu____2992 = FStar_Util.set_is_empty intersection
                         in
                      if uu____2992
                      then
                        let uu____2995 = pat_vars p2  in
                        FStar_Util.set_union out uu____2995
                      else
                        (let duplicate_bv =
                           let uu____3000 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3000  in
                         let uu____3003 =
                           let uu____3008 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3008)
                            in
                         FStar_Errors.raise_error uu____3003 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3028 = pat_vars p1  in
              FStar_All.pipe_right uu____3028 (fun a238  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3056 =
                  let uu____3057 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3057  in
                if uu____3056
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3064 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3064  in
                   let first_nonlinear_var =
                     let uu____3068 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3068  in
                   let uu____3071 =
                     let uu____3076 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3076)  in
                   FStar_Errors.raise_error uu____3071 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3080) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3081) -> ()
         | (true ,uu____3088) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3111 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____3111 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3127 ->
               let uu____3130 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____3130 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3242 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____3258 =
                 let uu____3259 =
                   let uu____3260 =
                     let uu____3267 =
                       let uu____3268 =
                         let uu____3273 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____3273, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____3268  in
                     (uu____3267, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____3260  in
                 {
                   FStar_Parser_AST.pat = uu____3259;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____3258
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____3290 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____3291 = aux loc env1 p2  in
                 match uu____3291 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___114_3349 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___115_3354 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___115_3354.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___115_3354.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___114_3349.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___116_3356 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___117_3361 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___117_3361.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___117_3361.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___116_3356.FStar_Syntax_Syntax.p)
                           }
                       | uu____3362 when top -> p4
                       | uu____3363 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____3366 =
                       match binder with
                       | LetBinder uu____3379 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____3399 = close_fun env1 t  in
                             desugar_term env1 uu____3399  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____3401 -> true)
                            then
                              (let uu____3402 =
                                 let uu____3407 =
                                   let uu____3408 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____3409 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____3410 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3408 uu____3409 uu____3410
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3407)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3402)
                            else ();
                            (let uu____3412 = annot_pat_var p3 t1  in
                             (uu____3412,
                               (LocalBinder
                                  ((let uu___118_3418 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___118_3418.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___118_3418.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____3366 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3440 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3440, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3449 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3449, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3468 = resolvex loc env1 x  in
               (match uu____3468 with
                | (loc1,env2,xbv) ->
                    let uu____3490 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3490, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3509 = resolvex loc env1 x  in
               (match uu____3509 with
                | (loc1,env2,xbv) ->
                    let uu____3531 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3531, imp))
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
               let uu____3541 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3541, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3563;_},args)
               ->
               let uu____3569 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3610  ->
                        match uu____3610 with
                        | (loc1,env2,args1) ->
                            let uu____3658 = aux loc1 env2 arg  in
                            (match uu____3658 with
                             | (loc2,env3,uu____3687,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____3569 with
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
                    let uu____3757 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3757, false))
           | FStar_Parser_AST.PatApp uu____3772 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3794 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3827  ->
                        match uu____3827 with
                        | (loc1,env2,pats1) ->
                            let uu____3859 = aux loc1 env2 pat  in
                            (match uu____3859 with
                             | (loc2,env3,uu____3884,pat1,uu____3886) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3794 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3929 =
                        let uu____3932 =
                          let uu____3939 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3939  in
                        let uu____3940 =
                          let uu____3941 =
                            let uu____3954 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3954, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3941  in
                        FStar_All.pipe_left uu____3932 uu____3940  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3986 =
                               let uu____3987 =
                                 let uu____4000 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____4000, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3987  in
                             FStar_All.pipe_left (pos_r r) uu____3986) pats1
                        uu____3929
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
               let uu____4042 =
                 FStar_List.fold_left
                   (fun uu____4082  ->
                      fun p2  ->
                        match uu____4082 with
                        | (loc1,env2,pats) ->
                            let uu____4131 = aux loc1 env2 p2  in
                            (match uu____4131 with
                             | (loc2,env3,uu____4160,pat,uu____4162) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4042 with
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
                    let uu____4257 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____4257 with
                     | (constr,uu____4279) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____4282 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____4284 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____4284, false)))
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
                      (fun uu____4353  ->
                         match uu____4353 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4383  ->
                         match uu____4383 with
                         | (f,uu____4389) ->
                             let uu____4390 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4416  ->
                                       match uu____4416 with
                                       | (g,uu____4422) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____4390 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4427,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____4434 =
                   let uu____4435 =
                     let uu____4442 =
                       let uu____4443 =
                         let uu____4444 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____4444  in
                       FStar_Parser_AST.mk_pattern uu____4443
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____4442, args)  in
                   FStar_Parser_AST.PatApp uu____4435  in
                 FStar_Parser_AST.mk_pattern uu____4434
                   p1.FStar_Parser_AST.prange
                  in
               let uu____4447 = aux loc env1 app  in
               (match uu____4447 with
                | (env2,e,b,p2,uu____4476) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4504 =
                            let uu____4505 =
                              let uu____4518 =
                                let uu___119_4519 = fv  in
                                let uu____4520 =
                                  let uu____4523 =
                                    let uu____4524 =
                                      let uu____4531 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4531)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4524
                                     in
                                  FStar_Pervasives_Native.Some uu____4523  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___119_4519.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___119_4519.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4520
                                }  in
                              (uu____4518, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____4505  in
                          FStar_All.pipe_left pos uu____4504
                      | uu____4558 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4612 = aux' true loc env1 p2  in
               (match uu____4612 with
                | (loc1,env2,var,p3,uu____4639) ->
                    let uu____4644 =
                      FStar_List.fold_left
                        (fun uu____4676  ->
                           fun p4  ->
                             match uu____4676 with
                             | (loc2,env3,ps1) ->
                                 let uu____4709 = aux' true loc2 env3 p4  in
                                 (match uu____4709 with
                                  | (loc3,env4,uu____4734,p5,uu____4736) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____4644 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4787 ->
               let uu____4788 = aux' true loc env1 p1  in
               (match uu____4788 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4828 = aux_maybe_or env p  in
         match uu____4828 with
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
            let uu____4887 =
              let uu____4888 =
                let uu____4899 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4899,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4888  in
            (env, uu____4887, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4927 =
                  let uu____4928 =
                    let uu____4933 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4933, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4928  in
                mklet uu____4927
            | FStar_Parser_AST.PatVar (x,uu____4935) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4941);
                   FStar_Parser_AST.prange = uu____4942;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4962 =
                  let uu____4963 =
                    let uu____4974 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____4975 =
                      let uu____4982 = desugar_term env t  in
                      (uu____4982, tacopt1)  in
                    (uu____4974, uu____4975)  in
                  LetBinder uu____4963  in
                (env, uu____4962, [])
            | uu____4993 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5003 = desugar_data_pat env p is_mut  in
             match uu____5003 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5032;
                       FStar_Syntax_Syntax.p = uu____5033;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5034;
                       FStar_Syntax_Syntax.p = uu____5035;_}::[] -> []
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
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term)
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____5261 =
              let uu____5270 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____5270 l  in
            match uu____5261 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____5325;
                              FStar_Syntax_Syntax.vars = uu____5326;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5349 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5349 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5357 =
                                 let uu____5358 =
                                   let uu____5361 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____5361  in
                                 uu____5358.FStar_Syntax_Syntax.n  in
                               match uu____5357 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____5377))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5378 -> msg
                             else msg  in
                           let uu____5380 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5380
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5383 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5383 " is deprecated"  in
                           let uu____5384 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5384
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5385 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____5388 =
                      let uu____5389 =
                        let uu____5396 = mk_ref_read tm1  in
                        (uu____5396,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____5389  in
                    FStar_All.pipe_left mk1 uu____5388
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____5414 =
          let uu____5415 = unparen t  in uu____5415.FStar_Parser_AST.tm  in
        match uu____5414 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5416; FStar_Ident.ident = uu____5417;
              FStar_Ident.nsstr = uu____5418; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5421 ->
            let uu____5422 =
              let uu____5427 =
                let uu____5428 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5428  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5427)  in
            FStar_Errors.raise_error uu____5422 t.FStar_Parser_AST.range
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
          let uu___121_5523 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___121_5523.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___121_5523.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5526 =
          let uu____5527 = unparen top  in uu____5527.FStar_Parser_AST.tm  in
        match uu____5526 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5532 ->
            let uu____5539 = desugar_formula env top  in (uu____5539, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____5546 = desugar_formula env t  in (uu____5546, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____5553 = desugar_formula env t  in (uu____5553, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____5577 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____5577, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5579 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____5579, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____5587 =
                let uu____5588 =
                  let uu____5595 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____5595, args)  in
                FStar_Parser_AST.Op uu____5588  in
              FStar_Parser_AST.mk_term uu____5587 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____5598 =
              let uu____5599 =
                let uu____5600 =
                  let uu____5607 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____5607, [e])  in
                FStar_Parser_AST.Op uu____5600  in
              FStar_Parser_AST.mk_term uu____5599 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____5598
        | FStar_Parser_AST.Op (op_star,uu____5611::uu____5612::[]) when
            (let uu____5617 = FStar_Ident.text_of_id op_star  in
             uu____5617 = "*") &&
              (let uu____5619 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5619 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5634;_},t1::t2::[])
                  ->
                  let uu____5639 = flatten1 t1  in
                  FStar_List.append uu____5639 [t2]
              | uu____5642 -> [t]  in
            let uu____5643 =
              let uu____5668 =
                let uu____5675 =
                  let uu____5678 = unparen top  in flatten1 uu____5678  in
                FStar_All.pipe_right uu____5675
                  (FStar_List.map
                     (fun t  ->
                        let uu____5697 = desugar_typ_aq env t  in
                        match uu____5697 with
                        | (t',aq) ->
                            let uu____5708 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5708, aq)))
                 in
              FStar_All.pipe_right uu____5668 FStar_List.unzip  in
            (match uu____5643 with
             | (targs,aqs) ->
                 let uu____5785 =
                   let uu____5790 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5790
                    in
                 (match uu____5785 with
                  | (tup,uu____5806) ->
                      let uu____5807 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5807, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5819 =
              let uu____5820 =
                let uu____5823 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5823  in
              FStar_All.pipe_left setpos uu____5820  in
            (uu____5819, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5835 =
              let uu____5840 =
                let uu____5841 =
                  let uu____5842 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____5842 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____5841  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5840)  in
            FStar_Errors.raise_error uu____5835 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5853 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5853 with
             | FStar_Pervasives_Native.None  ->
                 let uu____5860 =
                   let uu____5865 =
                     let uu____5866 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5866
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5865)
                    in
                 FStar_Errors.raise_error uu____5860
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5876 =
                     let uu____5901 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____5943 = desugar_term_aq env t  in
                               match uu____5943 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____5901 FStar_List.unzip  in
                   (match uu____5876 with
                    | (args1,aqs) ->
                        let uu____6056 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6056, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6070)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6085 =
              let uu___122_6086 = top  in
              let uu____6087 =
                let uu____6088 =
                  let uu____6095 =
                    let uu___123_6096 = top  in
                    let uu____6097 =
                      let uu____6098 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6098  in
                    {
                      FStar_Parser_AST.tm = uu____6097;
                      FStar_Parser_AST.range =
                        (uu___123_6096.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___123_6096.FStar_Parser_AST.level)
                    }  in
                  (uu____6095, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6088  in
              {
                FStar_Parser_AST.tm = uu____6087;
                FStar_Parser_AST.range =
                  (uu___122_6086.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___122_6086.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6085
        | FStar_Parser_AST.Construct (n1,(a,uu____6101)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6117 =
                let uu___124_6118 = top  in
                let uu____6119 =
                  let uu____6120 =
                    let uu____6127 =
                      let uu___125_6128 = top  in
                      let uu____6129 =
                        let uu____6130 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____6130  in
                      {
                        FStar_Parser_AST.tm = uu____6129;
                        FStar_Parser_AST.range =
                          (uu___125_6128.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___125_6128.FStar_Parser_AST.level)
                      }  in
                    (uu____6127, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____6120  in
                {
                  FStar_Parser_AST.tm = uu____6119;
                  FStar_Parser_AST.range =
                    (uu___124_6118.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___124_6118.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____6117))
        | FStar_Parser_AST.Construct (n1,(a,uu____6133)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6148 =
              let uu___126_6149 = top  in
              let uu____6150 =
                let uu____6151 =
                  let uu____6158 =
                    let uu___127_6159 = top  in
                    let uu____6160 =
                      let uu____6161 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6161  in
                    {
                      FStar_Parser_AST.tm = uu____6160;
                      FStar_Parser_AST.range =
                        (uu___127_6159.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___127_6159.FStar_Parser_AST.level)
                    }  in
                  (uu____6158, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6151  in
              {
                FStar_Parser_AST.tm = uu____6150;
                FStar_Parser_AST.range =
                  (uu___126_6149.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___126_6149.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6148
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6162; FStar_Ident.ident = uu____6163;
              FStar_Ident.nsstr = uu____6164; FStar_Ident.str = "Type0";_}
            ->
            let uu____6167 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____6167, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6168; FStar_Ident.ident = uu____6169;
              FStar_Ident.nsstr = uu____6170; FStar_Ident.str = "Type";_}
            ->
            let uu____6173 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____6173, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6174; FStar_Ident.ident = uu____6175;
               FStar_Ident.nsstr = uu____6176; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____6194 =
              let uu____6195 =
                let uu____6196 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____6196  in
              mk1 uu____6195  in
            (uu____6194, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6197; FStar_Ident.ident = uu____6198;
              FStar_Ident.nsstr = uu____6199; FStar_Ident.str = "Effect";_}
            ->
            let uu____6202 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____6202, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6203; FStar_Ident.ident = uu____6204;
              FStar_Ident.nsstr = uu____6205; FStar_Ident.str = "True";_}
            ->
            let uu____6208 =
              let uu____6209 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6209
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6208, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6210; FStar_Ident.ident = uu____6211;
              FStar_Ident.nsstr = uu____6212; FStar_Ident.str = "False";_}
            ->
            let uu____6215 =
              let uu____6216 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6216
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6215, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____6219;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____6221 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____6221 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____6230 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_defined_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____6230, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____6231 =
                    let uu____6232 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____6232 txt
                     in
                  failwith uu____6231))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6239 = desugar_name mk1 setpos env true l  in
              (uu____6239, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6242 = desugar_name mk1 setpos env true l  in
              (uu____6242, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____6253 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____6253 with
                | FStar_Pervasives_Native.Some uu____6262 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____6267 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____6267 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6281 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____6298 =
                    let uu____6299 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____6299  in
                  (uu____6298, noaqs)
              | uu____6300 ->
                  let uu____6307 =
                    let uu____6312 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6312)  in
                  FStar_Errors.raise_error uu____6307
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6319 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____6319 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6326 =
                    let uu____6331 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6331)
                     in
                  FStar_Errors.raise_error uu____6326
                    top.FStar_Parser_AST.range
              | uu____6336 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____6340 = desugar_name mk1 setpos env true lid'  in
                  (uu____6340, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6356 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6356 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6375 ->
                       let uu____6382 =
                         FStar_Util.take
                           (fun uu____6406  ->
                              match uu____6406 with
                              | (uu____6411,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____6382 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____6456 =
                              let uu____6481 =
                                FStar_List.map
                                  (fun uu____6514  ->
                                     match uu____6514 with
                                     | (t,imp) ->
                                         let uu____6531 =
                                           desugar_term_aq env t  in
                                         (match uu____6531 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____6481
                                FStar_List.unzip
                               in
                            (match uu____6456 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____6652 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____6652, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____6668 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____6668 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6675 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6686 =
              FStar_List.fold_left
                (fun uu____6731  ->
                   fun b  ->
                     match uu____6731 with
                     | (env1,tparams,typs) ->
                         let uu____6788 = desugar_binder env1 b  in
                         (match uu____6788 with
                          | (xopt,t1) ->
                              let uu____6817 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6826 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6826)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6817 with
                               | (env2,x) ->
                                   let uu____6846 =
                                     let uu____6849 =
                                       let uu____6852 =
                                         let uu____6853 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____6853
                                          in
                                       [uu____6852]  in
                                     FStar_List.append typs uu____6849  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___128_6879 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___128_6879.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___128_6879.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6846)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6686 with
             | (env1,uu____6907,targs) ->
                 let uu____6929 =
                   let uu____6934 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____6934
                    in
                 (match uu____6929 with
                  | (tup,uu____6944) ->
                      let uu____6945 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____6945, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____6962 = uncurry binders t  in
            (match uu____6962 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___94_7004 =
                   match uu___94_7004 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7016 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7016
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7038 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7038 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7047 = aux env [] bs  in (uu____7047, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7054 = desugar_binder env b  in
            (match uu____7054 with
             | (FStar_Pervasives_Native.None ,uu____7065) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7079 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____7079 with
                  | ((x,uu____7089),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____7092 =
                        let uu____7093 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____7093  in
                      (uu____7092, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____7111 =
              FStar_List.fold_left
                (fun uu____7131  ->
                   fun pat  ->
                     match uu____7131 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____7157,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____7167 =
                                let uu____7170 = free_type_vars env1 t  in
                                FStar_List.append uu____7170 ftvs  in
                              (env1, uu____7167)
                          | FStar_Parser_AST.PatAscribed
                              (uu____7175,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____7186 =
                                let uu____7189 = free_type_vars env1 t  in
                                let uu____7192 =
                                  let uu____7195 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____7195 ftvs  in
                                FStar_List.append uu____7189 uu____7192  in
                              (env1, uu____7186)
                          | uu____7200 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____7111 with
             | (uu____7209,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____7221 =
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
                   FStar_List.append uu____7221 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___95_7276 =
                   match uu___95_7276 with
                   | [] ->
                       let uu____7301 = desugar_term_aq env1 body  in
                       (match uu____7301 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7338 =
                                      let uu____7339 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7339
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7338 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7402 =
                              let uu____7405 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7405  in
                            (uu____7402, aq))
                   | p::rest ->
                       let uu____7418 = desugar_binding_pat env1 p  in
                       (match uu____7418 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7452 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7459 =
                              match b with
                              | LetBinder uu____7496 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7562) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7616 =
                                          let uu____7623 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7623, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7616
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7679,uu____7680) ->
                                             let tup2 =
                                               let uu____7682 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7682
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7686 =
                                                 let uu____7693 =
                                                   let uu____7694 =
                                                     let uu____7709 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7712 =
                                                       let uu____7721 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7722 =
                                                         let uu____7725 =
                                                           let uu____7726 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7726
                                                            in
                                                         [uu____7725]  in
                                                       uu____7721 ::
                                                         uu____7722
                                                        in
                                                     (uu____7709, uu____7712)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7694
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7693
                                                  in
                                               uu____7686
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
                                            (uu____7786,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____7788,pats)) ->
                                             let tupn =
                                               let uu____7827 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7827
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7837 =
                                                 let uu____7838 =
                                                   let uu____7853 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____7856 =
                                                     let uu____7865 =
                                                       let uu____7874 =
                                                         let uu____7881 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7881
                                                          in
                                                       [uu____7874]  in
                                                     FStar_List.append args
                                                       uu____7865
                                                      in
                                                   (uu____7853, uu____7856)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____7838
                                                  in
                                               mk1 uu____7837  in
                                             let p2 =
                                               let uu____7919 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____7919
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____7960 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7459 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____8041,uu____8042,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____8064 =
                let uu____8065 = unparen e  in uu____8065.FStar_Parser_AST.tm
                 in
              match uu____8064 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____8075 ->
                  let uu____8076 = desugar_term_aq env e  in
                  (match uu____8076 with
                   | (head1,aq) ->
                       let uu____8089 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____8089, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____8096 ->
            let rec aux args aqs e =
              let uu____8175 =
                let uu____8176 = unparen e  in uu____8176.FStar_Parser_AST.tm
                 in
              match uu____8175 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____8196 = desugar_term_aq env t  in
                  (match uu____8196 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____8232 ->
                  let uu____8233 = desugar_term_aq env e  in
                  (match uu____8233 with
                   | (head1,aq) ->
                       let uu____8256 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____8256, (join_aqs (aq :: aqs))))
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
            let uu____8318 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____8318
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
            let uu____8370 = desugar_term_aq env t  in
            (match uu____8370 with
             | (tm,s) ->
                 let uu____8381 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____8381, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____8387 =
              let uu____8400 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____8400 then desugar_typ_aq else desugar_term_aq  in
            uu____8387 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8455 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8598  ->
                        match uu____8598 with
                        | (attr_opt,(p,def)) ->
                            let uu____8656 = is_app_pattern p  in
                            if uu____8656
                            then
                              let uu____8687 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8687, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____8769 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____8769, def1)
                               | uu____8814 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____8852);
                                           FStar_Parser_AST.prange =
                                             uu____8853;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____8901 =
                                            let uu____8922 =
                                              let uu____8927 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8927  in
                                            (uu____8922, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____8901, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____9018) ->
                                        if top_level
                                        then
                                          let uu____9053 =
                                            let uu____9074 =
                                              let uu____9079 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9079  in
                                            (uu____9074, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____9053, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____9169 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____9200 =
                FStar_List.fold_left
                  (fun uu____9273  ->
                     fun uu____9274  ->
                       match (uu____9273, uu____9274) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____9382,uu____9383),uu____9384))
                           ->
                           let uu____9501 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9527 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9527 with
                                  | (env2,xx) ->
                                      let uu____9546 =
                                        let uu____9549 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9549 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9546))
                             | FStar_Util.Inr l ->
                                 let uu____9557 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____9557, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9501 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____9200 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9705 =
                    match uu____9705 with
                    | (attrs_opt,(uu____9741,args,result_t),def) ->
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
                                let uu____9829 = is_comp_type env1 t  in
                                if uu____9829
                                then
                                  ((let uu____9831 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____9841 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____9841))
                                       in
                                    match uu____9831 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____9844 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____9846 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____9846))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____9844
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____9850 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____9850 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____9854 ->
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
                              let uu____9869 =
                                let uu____9870 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____9870
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____9869
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
                  let uu____9945 = desugar_term_aq env' body  in
                  (match uu____9945 with
                   | (body1,aq) ->
                       let uu____9958 =
                         let uu____9961 =
                           let uu____9962 =
                             let uu____9975 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____9975)  in
                           FStar_Syntax_Syntax.Tm_let uu____9962  in
                         FStar_All.pipe_left mk1 uu____9961  in
                       (uu____9958, aq))
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
              let uu____10049 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____10049 with
              | (env1,binder,pat1) ->
                  let uu____10071 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____10097 = desugar_term_aq env1 t2  in
                        (match uu____10097 with
                         | (body1,aq) ->
                             let fv =
                               let uu____10111 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____10111
                                 FStar_Pervasives_Native.None
                                in
                             let uu____10112 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____10112, aq))
                    | LocalBinder (x,uu____10142) ->
                        let uu____10143 = desugar_term_aq env1 t2  in
                        (match uu____10143 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____10157;
                                   FStar_Syntax_Syntax.p = uu____10158;_}::[]
                                   -> body1
                               | uu____10159 ->
                                   let uu____10162 =
                                     let uu____10169 =
                                       let uu____10170 =
                                         let uu____10193 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____10196 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____10193, uu____10196)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____10170
                                        in
                                     FStar_Syntax_Syntax.mk uu____10169  in
                                   uu____10162 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____10236 =
                               let uu____10239 =
                                 let uu____10240 =
                                   let uu____10253 =
                                     let uu____10256 =
                                       let uu____10257 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____10257]  in
                                     FStar_Syntax_Subst.close uu____10256
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____10253)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____10240  in
                               FStar_All.pipe_left mk1 uu____10239  in
                             (uu____10236, aq))
                     in
                  (match uu____10071 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____10314 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____10314, aq)
                       else (tm, aq))
               in
            let uu____10326 = FStar_List.hd lbs  in
            (match uu____10326 with
             | (attrs,(head_pat,defn)) ->
                 let uu____10370 = is_rec || (is_app_pattern head_pat)  in
                 if uu____10370
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____10383 =
                let uu____10384 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____10384  in
              mk1 uu____10383  in
            let uu____10385 = desugar_term_aq env t1  in
            (match uu____10385 with
             | (t1',aq1) ->
                 let uu____10396 = desugar_term_aq env t2  in
                 (match uu____10396 with
                  | (t2',aq2) ->
                      let uu____10407 = desugar_term_aq env t3  in
                      (match uu____10407 with
                       | (t3',aq3) ->
                           let uu____10418 =
                             let uu____10419 =
                               let uu____10420 =
                                 let uu____10443 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None)
                                    in
                                 let uu____10464 =
                                   let uu____10481 =
                                     let uu____10494 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____10494,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____10505 =
                                     let uu____10520 =
                                       let uu____10533 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____10533,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____10520]  in
                                   uu____10481 :: uu____10505  in
                                 (uu____10443, uu____10464)  in
                               FStar_Syntax_Syntax.Tm_match uu____10420  in
                             mk1 uu____10419  in
                           (uu____10418, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10724 =
              match uu____10724 with
              | (pat,wopt,b) ->
                  let uu____10746 = desugar_match_pat env pat  in
                  (match uu____10746 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____10777 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____10777
                          in
                       let uu____10778 = desugar_term_aq env1 b  in
                       (match uu____10778 with
                        | (b1,aq) ->
                            let uu____10791 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____10791, aq)))
               in
            let uu____10796 = desugar_term_aq env e  in
            (match uu____10796 with
             | (e1,aq) ->
                 let uu____10807 =
                   let uu____10816 =
                     let uu____10827 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____10827 FStar_List.unzip  in
                   FStar_All.pipe_right uu____10816
                     (fun uu____10891  ->
                        match uu____10891 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____10807 with
                  | (brs,aqs) ->
                      let uu____10942 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____10942, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____10983 = is_comp_type env t  in
              if uu____10983
              then
                let uu____10988 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____10988
              else
                (let uu____10990 = desugar_term env t  in
                 FStar_Util.Inl uu____10990)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____10994 = desugar_term_aq env e  in
            (match uu____10994 with
             | (e1,aq) ->
                 let uu____11005 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____11005, aq))
        | FStar_Parser_AST.Record (uu____11032,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____11073 = FStar_List.hd fields  in
              match uu____11073 with | (f,uu____11085) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____11131  ->
                        match uu____11131 with
                        | (g,uu____11137) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____11143,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____11157 =
                         let uu____11162 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____11162)
                          in
                       FStar_Errors.raise_error uu____11157
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
                  let uu____11170 =
                    let uu____11181 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____11212  ->
                              match uu____11212 with
                              | (f,uu____11222) ->
                                  let uu____11223 =
                                    let uu____11224 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____11224
                                     in
                                  (uu____11223, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____11181)  in
                  FStar_Parser_AST.Construct uu____11170
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____11242 =
                      let uu____11243 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____11243  in
                    FStar_Parser_AST.mk_term uu____11242
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____11245 =
                      let uu____11258 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____11288  ->
                                match uu____11288 with
                                | (f,uu____11298) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____11258)  in
                    FStar_Parser_AST.Record uu____11245  in
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
            let uu____11358 = desugar_term_aq env recterm1  in
            (match uu____11358 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____11374;
                         FStar_Syntax_Syntax.vars = uu____11375;_},args)
                      ->
                      let uu____11397 =
                        let uu____11398 =
                          let uu____11399 =
                            let uu____11414 =
                              let uu____11417 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____11418 =
                                let uu____11421 =
                                  let uu____11422 =
                                    let uu____11429 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____11429)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____11422
                                   in
                                FStar_Pervasives_Native.Some uu____11421  in
                              FStar_Syntax_Syntax.fvar uu____11417
                                FStar_Syntax_Syntax.Delta_constant
                                uu____11418
                               in
                            (uu____11414, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____11399  in
                        FStar_All.pipe_left mk1 uu____11398  in
                      (uu____11397, s)
                  | uu____11456 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____11460 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____11460 with
              | (constrname,is_rec) ->
                  let uu____11475 = desugar_term_aq env e  in
                  (match uu____11475 with
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
                       let uu____11493 =
                         let uu____11494 =
                           let uu____11495 =
                             let uu____11510 =
                               let uu____11513 =
                                 let uu____11514 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____11514
                                  in
                               FStar_Syntax_Syntax.fvar uu____11513
                                 FStar_Syntax_Syntax.Delta_equational qual
                                in
                             let uu____11515 =
                               let uu____11524 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____11524]  in
                             (uu____11510, uu____11515)  in
                           FStar_Syntax_Syntax.Tm_app uu____11495  in
                         FStar_All.pipe_left mk1 uu____11494  in
                       (uu____11493, s))))
        | FStar_Parser_AST.NamedTyp (uu____11535,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____11544 =
              let uu____11545 = FStar_Syntax_Subst.compress tm  in
              uu____11545.FStar_Syntax_Syntax.n  in
            (match uu____11544 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____11553 =
                   let uu___129_11554 =
                     let uu____11555 =
                       let uu____11556 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____11556  in
                     FStar_Syntax_Util.exp_string uu____11555  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___129_11554.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___129_11554.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____11553, noaqs)
             | uu____11557 ->
                 let uu____11558 =
                   let uu____11563 =
                     let uu____11564 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____11564
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____11563)  in
                 FStar_Errors.raise_error uu____11558
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____11570 = desugar_term_aq env e  in
            (match uu____11570 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____11582 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____11582, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____11588 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____11589 =
              let uu____11590 =
                let uu____11597 = desugar_term env e  in (bv, b, uu____11597)
                 in
              [uu____11590]  in
            (uu____11588, uu____11589)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____11620 =
              let uu____11621 =
                let uu____11622 =
                  let uu____11629 = desugar_term env e  in (uu____11629, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____11622  in
              FStar_All.pipe_left mk1 uu____11621  in
            (uu____11620, noaqs)
        | uu____11634 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____11635 = desugar_formula env top  in
            (uu____11635, noaqs)
        | uu____11636 ->
            let uu____11637 =
              let uu____11642 =
                let uu____11643 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____11643  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____11642)  in
            FStar_Errors.raise_error uu____11637 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____11649 -> false
    | uu____11658 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____11664 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____11664 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____11668 -> false

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
           (fun uu____11705  ->
              match uu____11705 with
              | (a,imp) ->
                  let uu____11718 = desugar_term env a  in
                  arg_withimp_e imp uu____11718))

and (desugar_comp :
  FStar_Range.range ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.term -> FStar_Syntax_Syntax.comp)
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail1 err = FStar_Errors.raise_error err r  in
        let is_requires uu____11750 =
          match uu____11750 with
          | (t1,uu____11756) ->
              let uu____11757 =
                let uu____11758 = unparen t1  in
                uu____11758.FStar_Parser_AST.tm  in
              (match uu____11757 with
               | FStar_Parser_AST.Requires uu____11759 -> true
               | uu____11766 -> false)
           in
        let is_ensures uu____11776 =
          match uu____11776 with
          | (t1,uu____11782) ->
              let uu____11783 =
                let uu____11784 = unparen t1  in
                uu____11784.FStar_Parser_AST.tm  in
              (match uu____11783 with
               | FStar_Parser_AST.Ensures uu____11785 -> true
               | uu____11792 -> false)
           in
        let is_app head1 uu____11807 =
          match uu____11807 with
          | (t1,uu____11813) ->
              let uu____11814 =
                let uu____11815 = unparen t1  in
                uu____11815.FStar_Parser_AST.tm  in
              (match uu____11814 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____11817;
                      FStar_Parser_AST.level = uu____11818;_},uu____11819,uu____11820)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____11821 -> false)
           in
        let is_smt_pat uu____11831 =
          match uu____11831 with
          | (t1,uu____11837) ->
              let uu____11838 =
                let uu____11839 = unparen t1  in
                uu____11839.FStar_Parser_AST.tm  in
              (match uu____11838 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____11842);
                             FStar_Parser_AST.range = uu____11843;
                             FStar_Parser_AST.level = uu____11844;_},uu____11845)::uu____11846::[])
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
                             FStar_Parser_AST.range = uu____11885;
                             FStar_Parser_AST.level = uu____11886;_},uu____11887)::uu____11888::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____11913 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____11945 = head_and_args t1  in
          match uu____11945 with
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
                   let thunk_ens uu____12043 =
                     match uu____12043 with
                     | (e,i) ->
                         let uu____12054 = thunk_ens_ e  in (uu____12054, i)
                      in
                   let fail_lemma uu____12066 =
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
                         let uu____12146 =
                           let uu____12153 =
                             let uu____12160 = thunk_ens ens  in
                             [uu____12160; nil_pat]  in
                           req_true :: uu____12153  in
                         unit_tm :: uu____12146
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____12207 =
                           let uu____12214 =
                             let uu____12221 = thunk_ens ens  in
                             [uu____12221; nil_pat]  in
                           req :: uu____12214  in
                         unit_tm :: uu____12207
                     | ens::smtpat::[] when
                         (((let uu____12270 = is_requires ens  in
                            Prims.op_Negation uu____12270) &&
                             (let uu____12272 = is_smt_pat ens  in
                              Prims.op_Negation uu____12272))
                            &&
                            (let uu____12274 = is_decreases ens  in
                             Prims.op_Negation uu____12274))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____12275 =
                           let uu____12282 =
                             let uu____12289 = thunk_ens ens  in
                             [uu____12289; smtpat]  in
                           req_true :: uu____12282  in
                         unit_tm :: uu____12275
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____12336 =
                           let uu____12343 =
                             let uu____12350 = thunk_ens ens  in
                             [uu____12350; nil_pat; dec]  in
                           req_true :: uu____12343  in
                         unit_tm :: uu____12336
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12410 =
                           let uu____12417 =
                             let uu____12424 = thunk_ens ens  in
                             [uu____12424; smtpat; dec]  in
                           req_true :: uu____12417  in
                         unit_tm :: uu____12410
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____12484 =
                           let uu____12491 =
                             let uu____12498 = thunk_ens ens  in
                             [uu____12498; nil_pat; dec]  in
                           req :: uu____12491  in
                         unit_tm :: uu____12484
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12558 =
                           let uu____12565 =
                             let uu____12572 = thunk_ens ens  in
                             [uu____12572; smtpat]  in
                           req :: uu____12565  in
                         unit_tm :: uu____12558
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____12637 =
                           let uu____12644 =
                             let uu____12651 = thunk_ens ens  in
                             [uu____12651; dec; smtpat]  in
                           req :: uu____12644  in
                         unit_tm :: uu____12637
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____12713 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____12713, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12741 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12741
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____12742 =
                     let uu____12749 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12749, [])  in
                   (uu____12742, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12767 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12767
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____12768 =
                     let uu____12775 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12775, [])  in
                   (uu____12768, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____12791 =
                     let uu____12798 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12798, [])  in
                   (uu____12791, [(t1, FStar_Parser_AST.Nothing)])
               | uu____12821 ->
                   let default_effect =
                     let uu____12823 = FStar_Options.ml_ish ()  in
                     if uu____12823
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____12826 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____12826
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____12828 =
                     let uu____12835 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12835, [])  in
                   (uu____12828, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____12858 = pre_process_comp_typ t  in
        match uu____12858 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____12905 =
                  let uu____12910 =
                    let uu____12911 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____12911
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____12910)  in
                fail1 uu____12905)
             else ();
             (let is_universe uu____12922 =
                match uu____12922 with
                | (uu____12927,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____12929 = FStar_Util.take is_universe args  in
              match uu____12929 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____12986  ->
                         match uu____12986 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____12993 =
                    let uu____13008 = FStar_List.hd args1  in
                    let uu____13017 = FStar_List.tl args1  in
                    (uu____13008, uu____13017)  in
                  (match uu____12993 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____13070 =
                         let is_decrease uu____13108 =
                           match uu____13108 with
                           | (t1,uu____13118) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____13128;
                                       FStar_Syntax_Syntax.vars = uu____13129;_},uu____13130::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____13161 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____13070 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____13275  ->
                                      match uu____13275 with
                                      | (t1,uu____13285) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____13294,(arg,uu____13296)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____13325 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____13342 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____13353 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____13353
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____13355 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____13355
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____13360 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____13360
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____13364 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____13364
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____13368 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____13368
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____13372 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____13372
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____13388 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____13388
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
                                                  let uu____13473 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____13473
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
                                            | uu____13488 -> pat  in
                                          let uu____13489 =
                                            let uu____13500 =
                                              let uu____13511 =
                                                let uu____13520 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____13520, aq)  in
                                              [uu____13511]  in
                                            ens :: uu____13500  in
                                          req :: uu____13489
                                      | uu____13561 -> rest2
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
        | uu____13585 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___130_13606 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___130_13606.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___130_13606.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___131_13648 = b  in
             {
               FStar_Parser_AST.b = (uu___131_13648.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___131_13648.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___131_13648.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____13711 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____13711)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____13724 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____13724 with
             | (env1,a1) ->
                 let a2 =
                   let uu___132_13734 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___132_13734.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___132_13734.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____13760 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____13774 =
                     let uu____13777 =
                       let uu____13778 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____13778]  in
                     no_annot_abs uu____13777 body2  in
                   FStar_All.pipe_left setpos uu____13774  in
                 let uu____13793 =
                   let uu____13794 =
                     let uu____13809 =
                       let uu____13812 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____13812
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____13813 =
                       let uu____13822 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____13822]  in
                     (uu____13809, uu____13813)  in
                   FStar_Syntax_Syntax.Tm_app uu____13794  in
                 FStar_All.pipe_left mk1 uu____13793)
        | uu____13835 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____13915 = q (rest, pats, body)  in
              let uu____13922 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____13915 uu____13922
                FStar_Parser_AST.Formula
               in
            let uu____13923 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____13923 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____13932 -> failwith "impossible"  in
      let uu____13935 =
        let uu____13936 = unparen f  in uu____13936.FStar_Parser_AST.tm  in
      match uu____13935 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____13943,uu____13944) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____13955,uu____13956) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13987 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____13987
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____14023 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____14023
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____14066 -> desugar_term env f

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
      let uu____14071 =
        FStar_List.fold_left
          (fun uu____14107  ->
             fun b  ->
               match uu____14107 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___133_14159 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___133_14159.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___133_14159.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___133_14159.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____14176 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____14176 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___134_14196 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___134_14196.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___134_14196.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____14213 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____14071 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____14300 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14300)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____14305 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14305)
      | FStar_Parser_AST.TVariable x ->
          let uu____14309 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____14309)
      | FStar_Parser_AST.NoName t ->
          let uu____14313 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____14313)
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
               (fun uu___96_14352  ->
                  match uu___96_14352 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____14353 -> false))
           in
        let quals2 q =
          let uu____14366 =
            (let uu____14369 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____14369) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____14366
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____14383 = FStar_Ident.range_of_lid disc_name  in
                let uu____14384 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____14383;
                  FStar_Syntax_Syntax.sigquals = uu____14384;
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
            let uu____14423 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____14457  ->
                        match uu____14457 with
                        | (x,uu____14465) ->
                            let uu____14466 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____14466 with
                             | (field_name,uu____14474) ->
                                 let only_decl =
                                   ((let uu____14478 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____14478)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____14480 =
                                        let uu____14481 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____14481.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____14480)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____14497 =
                                       FStar_List.filter
                                         (fun uu___97_14501  ->
                                            match uu___97_14501 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____14502 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____14497
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___98_14515  ->
                                             match uu___98_14515 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____14516 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____14518 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____14518;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____14523 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____14523
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____14528 =
                                        let uu____14533 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____14533  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____14528;
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
                                      let uu____14537 =
                                        let uu____14538 =
                                          let uu____14545 =
                                            let uu____14548 =
                                              let uu____14549 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____14549
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____14548]  in
                                          ((false, [lb]), uu____14545)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____14538
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____14537;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____14423 FStar_List.flatten
  
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
            (lid,uu____14593,t,uu____14595,n1,uu____14597) when
            let uu____14602 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____14602 ->
            let uu____14603 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____14603 with
             | (formals,uu____14619) ->
                 (match formals with
                  | [] -> []
                  | uu____14642 ->
                      let filter_records uu___99_14656 =
                        match uu___99_14656 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____14659,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____14671 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____14673 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____14673 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____14683 = FStar_Util.first_N n1 formals  in
                      (match uu____14683 with
                       | (uu____14706,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____14732 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.binders ->
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
                    let uu____14790 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____14790
                    then
                      let uu____14793 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____14793
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____14796 =
                      let uu____14801 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____14801  in
                    let uu____14802 =
                      let uu____14805 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____14805  in
                    let uu____14806 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____14796;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____14802;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____14806;
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
          let tycon_id uu___100_14857 =
            match uu___100_14857 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____14859,uu____14860) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____14870,uu____14871,uu____14872) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____14882,uu____14883,uu____14884) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____14914,uu____14915,uu____14916) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____14960) ->
                let uu____14961 =
                  let uu____14962 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14962  in
                FStar_Parser_AST.mk_term uu____14961 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____14964 =
                  let uu____14965 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14965  in
                FStar_Parser_AST.mk_term uu____14964 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____14967) ->
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
              | uu____14998 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____15004 =
                     let uu____15005 =
                       let uu____15012 = binder_to_term b  in
                       (out, uu____15012, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____15005  in
                   FStar_Parser_AST.mk_term uu____15004
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___101_15024 =
            match uu___101_15024 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____15080  ->
                       match uu____15080 with
                       | (x,t,uu____15091) ->
                           let uu____15096 =
                             let uu____15097 =
                               let uu____15102 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____15102, t)  in
                             FStar_Parser_AST.Annotated uu____15097  in
                           FStar_Parser_AST.mk_binder uu____15096
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____15104 =
                    let uu____15105 =
                      let uu____15106 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____15106  in
                    FStar_Parser_AST.mk_term uu____15105
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____15104 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____15110 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____15137  ->
                          match uu____15137 with
                          | (x,uu____15147,uu____15148) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____15110)
            | uu____15201 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___102_15240 =
            match uu___102_15240 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____15264 = typars_of_binders _env binders  in
                (match uu____15264 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____15306 =
                         let uu____15307 =
                           let uu____15308 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____15308  in
                         FStar_Parser_AST.mk_term uu____15307
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____15306 binders  in
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
            | uu____15319 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____15367 =
              FStar_List.fold_left
                (fun uu____15407  ->
                   fun uu____15408  ->
                     match (uu____15407, uu____15408) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____15499 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____15499 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____15367 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____15612 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____15612
                | uu____15613 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____15621 = desugar_abstract_tc quals env [] tc  in
              (match uu____15621 with
               | (uu____15634,uu____15635,se,uu____15637) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____15640,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____15657 =
                                 let uu____15658 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____15658  in
                               if uu____15657
                               then
                                 let uu____15659 =
                                   let uu____15664 =
                                     let uu____15665 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____15665
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____15664)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____15659
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
                           | uu____15672 ->
                               let uu____15673 =
                                 let uu____15680 =
                                   let uu____15681 =
                                     let uu____15694 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____15694)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____15681
                                    in
                                 FStar_Syntax_Syntax.mk uu____15680  in
                               uu____15673 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___135_15708 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___135_15708.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___135_15708.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___135_15708.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____15709 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____15712 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____15712
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____15725 = typars_of_binders env binders  in
              (match uu____15725 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15761 =
                           FStar_Util.for_some
                             (fun uu___103_15763  ->
                                match uu___103_15763 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____15764 -> false) quals
                            in
                         if uu____15761
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____15771 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___104_15775  ->
                               match uu___104_15775 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____15776 -> false))
                        in
                     if uu____15771
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____15785 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____15785
                     then
                       let uu____15788 =
                         let uu____15795 =
                           let uu____15796 = unparen t  in
                           uu____15796.FStar_Parser_AST.tm  in
                         match uu____15795 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____15817 =
                               match FStar_List.rev args with
                               | (last_arg,uu____15847)::args_rev ->
                                   let uu____15859 =
                                     let uu____15860 = unparen last_arg  in
                                     uu____15860.FStar_Parser_AST.tm  in
                                   (match uu____15859 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____15888 -> ([], args))
                               | uu____15897 -> ([], args)  in
                             (match uu____15817 with
                              | (cattributes,args1) ->
                                  let uu____15936 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____15936))
                         | uu____15947 -> (t, [])  in
                       match uu____15788 with
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
                                  (fun uu___105_15967  ->
                                     match uu___105_15967 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____15968 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____15975)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____15999 = tycon_record_as_variant trec  in
              (match uu____15999 with
               | (t,fs) ->
                   let uu____16016 =
                     let uu____16019 =
                       let uu____16020 =
                         let uu____16029 =
                           let uu____16032 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____16032  in
                         (uu____16029, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____16020  in
                     uu____16019 :: quals  in
                   desugar_tycon env d uu____16016 [t])
          | uu____16037::uu____16038 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____16205 = et  in
                match uu____16205 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____16430 ->
                         let trec = tc  in
                         let uu____16454 = tycon_record_as_variant trec  in
                         (match uu____16454 with
                          | (t,fs) ->
                              let uu____16513 =
                                let uu____16516 =
                                  let uu____16517 =
                                    let uu____16526 =
                                      let uu____16529 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____16529  in
                                    (uu____16526, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____16517
                                   in
                                uu____16516 :: quals1  in
                              collect_tcs uu____16513 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____16616 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16616 with
                          | (env2,uu____16676,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____16825 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16825 with
                          | (env2,uu____16885,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____17010 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____17057 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____17057 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___107_17568  ->
                             match uu___107_17568 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____17635,uu____17636);
                                    FStar_Syntax_Syntax.sigrng = uu____17637;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____17638;
                                    FStar_Syntax_Syntax.sigmeta = uu____17639;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17640;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____17701 =
                                     typars_of_binders env1 binders  in
                                   match uu____17701 with
                                   | (env2,tpars1) ->
                                       let uu____17732 =
                                         push_tparams env2 tpars1  in
                                       (match uu____17732 with
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
                                 let uu____17765 =
                                   let uu____17786 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____17786)
                                    in
                                 [uu____17765]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____17854);
                                    FStar_Syntax_Syntax.sigrng = uu____17855;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____17857;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17858;_},constrs,tconstr,quals1)
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
                                 let uu____17956 = push_tparams env1 tpars
                                    in
                                 (match uu____17956 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____18033  ->
                                             match uu____18033 with
                                             | (x,uu____18047) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____18055 =
                                        let uu____18084 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____18198  ->
                                                  match uu____18198 with
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
                                                        let uu____18254 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____18254
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
                                                                uu___106_18265
                                                                 ->
                                                                match uu___106_18265
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____18277
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____18285 =
                                                        let uu____18306 =
                                                          let uu____18307 =
                                                            let uu____18308 =
                                                              let uu____18323
                                                                =
                                                                let uu____18324
                                                                  =
                                                                  let uu____18325
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____18325
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____18324
                                                                 in
                                                              (name, univs1,
                                                                uu____18323,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____18308
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____18307;
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
                                                          uu____18306)
                                                         in
                                                      (name, uu____18285)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____18084
                                         in
                                      (match uu____18055 with
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
                             | uu____18562 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18694  ->
                             match uu____18694 with
                             | (name_doc,uu____18722,uu____18723) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18803  ->
                             match uu____18803 with
                             | (uu____18824,uu____18825,se) -> se))
                      in
                   let uu____18855 =
                     let uu____18862 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____18862 rng
                      in
                   (match uu____18855 with
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
                               (fun uu____18928  ->
                                  match uu____18928 with
                                  | (uu____18951,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____19002,tps,k,uu____19005,constrs)
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
                                  | uu____19024 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____19041  ->
                                 match uu____19041 with
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
      let uu____19078 =
        FStar_List.fold_left
          (fun uu____19101  ->
             fun b  ->
               match uu____19101 with
               | (env1,binders1) ->
                   let uu____19121 = desugar_binder env1 b  in
                   (match uu____19121 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19138 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____19138 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____19155 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____19078 with
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
          let uu____19208 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___108_19213  ->
                    match uu___108_19213 with
                    | FStar_Syntax_Syntax.Reflectable uu____19214 -> true
                    | uu____19215 -> false))
             in
          if uu____19208
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____19218 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____19218
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
                  let uu____19360 = desugar_binders monad_env eff_binders  in
                  match uu____19360 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____19381 =
                          let uu____19382 =
                            let uu____19389 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____19389  in
                          FStar_List.length uu____19382  in
                        uu____19381 = (Prims.parse_int "1")  in
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
                            (uu____19433,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____19435,uu____19436,uu____19437),uu____19438)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____19471 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____19472 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____19484 = name_of_eff_decl decl  in
                             FStar_List.mem uu____19484 mandatory_members)
                          eff_decls
                         in
                      (match uu____19472 with
                       | (mandatory_members_decls,actions) ->
                           let uu____19501 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____19530  ->
                                     fun decl  ->
                                       match uu____19530 with
                                       | (env2,out) ->
                                           let uu____19550 =
                                             desugar_decl env2 decl  in
                                           (match uu____19550 with
                                            | (env3,ses) ->
                                                let uu____19563 =
                                                  let uu____19566 =
                                                    FStar_List.hd ses  in
                                                  uu____19566 :: out  in
                                                (env3, uu____19563)))
                                  (env1, []))
                              in
                           (match uu____19501 with
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
                                              (uu____19634,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____19637,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____19638,
                                                                  (def,uu____19640)::
                                                                  (cps_type,uu____19642)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____19643;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____19644;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____19696 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19696 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19716 =
                                                     let uu____19717 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19718 =
                                                       let uu____19719 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19719
                                                        in
                                                     let uu____19724 =
                                                       let uu____19725 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19725
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19717;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19718;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____19724
                                                     }  in
                                                   (uu____19716, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____19732,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____19735,defn),doc1)::[])
                                              when for_free ->
                                              let uu____19770 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19770 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19790 =
                                                     let uu____19791 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19792 =
                                                       let uu____19793 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19793
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19791;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19792;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____19790, doc1))
                                          | uu____19800 ->
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
                                    let uu____19832 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____19832
                                     in
                                  let uu____19833 =
                                    let uu____19834 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____19834
                                     in
                                  ([], uu____19833)  in
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
                                      let uu____19851 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____19851)  in
                                    let uu____19858 =
                                      let uu____19859 =
                                        let uu____19860 =
                                          let uu____19861 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19861
                                           in
                                        let uu____19870 = lookup1 "return"
                                           in
                                        let uu____19871 = lookup1 "bind"  in
                                        let uu____19872 =
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
                                            uu____19860;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____19870;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____19871;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____19872
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____19859
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____19858;
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
                                         (fun uu___109_19878  ->
                                            match uu___109_19878 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____19879 -> true
                                            | uu____19880 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____19894 =
                                       let uu____19895 =
                                         let uu____19896 =
                                           lookup1 "return_wp"  in
                                         let uu____19897 = lookup1 "bind_wp"
                                            in
                                         let uu____19898 =
                                           lookup1 "if_then_else"  in
                                         let uu____19899 = lookup1 "ite_wp"
                                            in
                                         let uu____19900 = lookup1 "stronger"
                                            in
                                         let uu____19901 = lookup1 "close_wp"
                                            in
                                         let uu____19902 = lookup1 "assert_p"
                                            in
                                         let uu____19903 = lookup1 "assume_p"
                                            in
                                         let uu____19904 = lookup1 "null_wp"
                                            in
                                         let uu____19905 = lookup1 "trivial"
                                            in
                                         let uu____19906 =
                                           if rr
                                           then
                                             let uu____19907 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____19907
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____19923 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____19925 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____19927 =
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
                                             uu____19896;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____19897;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____19898;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____19899;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____19900;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____19901;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____19902;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____19903;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____19904;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____19905;
                                           FStar_Syntax_Syntax.repr =
                                             uu____19906;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____19923;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____19925;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____19927
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____19895
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____19894;
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
                                          fun uu____19953  ->
                                            match uu____19953 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____19967 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____19967
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
                let uu____19991 = desugar_binders env1 eff_binders  in
                match uu____19991 with
                | (env2,binders) ->
                    let uu____20010 =
                      let uu____20029 = head_and_args defn  in
                      match uu____20029 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____20074 ->
                                let uu____20075 =
                                  let uu____20080 =
                                    let uu____20081 =
                                      let uu____20082 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____20082 " not found"
                                       in
                                    Prims.strcat "Effect " uu____20081  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____20080)
                                   in
                                FStar_Errors.raise_error uu____20075
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____20084 =
                            match FStar_List.rev args with
                            | (last_arg,uu____20114)::args_rev ->
                                let uu____20126 =
                                  let uu____20127 = unparen last_arg  in
                                  uu____20127.FStar_Parser_AST.tm  in
                                (match uu____20126 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____20155 -> ([], args))
                            | uu____20164 -> ([], args)  in
                          (match uu____20084 with
                           | (cattributes,args1) ->
                               let uu____20215 = desugar_args env2 args1  in
                               let uu____20224 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____20215, uu____20224))
                       in
                    (match uu____20010 with
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
                          (let uu____20280 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____20280 with
                           | (ed_binders,uu____20294,ed_binders_opening) ->
                               let sub1 uu____20307 =
                                 match uu____20307 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____20321 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____20321 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____20325 =
                                       let uu____20326 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____20326)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____20325
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____20335 =
                                   let uu____20336 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____20336
                                    in
                                 let uu____20351 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____20352 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____20353 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____20354 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____20355 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____20356 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____20357 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____20358 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____20359 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____20360 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____20361 =
                                   let uu____20362 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____20362
                                    in
                                 let uu____20377 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____20378 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____20379 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____20387 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____20388 =
                                          let uu____20389 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____20389
                                           in
                                        let uu____20404 =
                                          let uu____20405 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____20405
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____20387;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____20388;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____20404
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
                                     uu____20335;
                                   FStar_Syntax_Syntax.ret_wp = uu____20351;
                                   FStar_Syntax_Syntax.bind_wp = uu____20352;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____20353;
                                   FStar_Syntax_Syntax.ite_wp = uu____20354;
                                   FStar_Syntax_Syntax.stronger = uu____20355;
                                   FStar_Syntax_Syntax.close_wp = uu____20356;
                                   FStar_Syntax_Syntax.assert_p = uu____20357;
                                   FStar_Syntax_Syntax.assume_p = uu____20358;
                                   FStar_Syntax_Syntax.null_wp = uu____20359;
                                   FStar_Syntax_Syntax.trivial = uu____20360;
                                   FStar_Syntax_Syntax.repr = uu____20361;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____20377;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____20378;
                                   FStar_Syntax_Syntax.actions = uu____20379;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____20422 =
                                     let uu____20423 =
                                       let uu____20430 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____20430
                                        in
                                     FStar_List.length uu____20423  in
                                   uu____20422 = (Prims.parse_int "1")  in
                                 let uu____20459 =
                                   let uu____20462 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____20462 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____20459;
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
                                             let uu____20484 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____20484
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____20486 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____20486
                                 then
                                   let reflect_lid =
                                     let uu____20490 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____20490
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
    let uu____20500 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____20500 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____20551 ->
              let uu____20552 =
                let uu____20553 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____20553
                 in
              Prims.strcat "\n  " uu____20552
          | uu____20554 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____20567  ->
               match uu____20567 with
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
          let uu____20585 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____20585
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____20587 =
          let uu____20596 = FStar_Syntax_Syntax.as_arg arg  in [uu____20596]
           in
        FStar_Syntax_Util.mk_app fv uu____20587

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____20621 = desugar_decl_noattrs env d  in
      match uu____20621 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____20639 = mk_comment_attr d  in uu____20639 :: attrs1  in
          let uu____20640 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___136_20644 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___136_20644.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___136_20644.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___136_20644.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___136_20644.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____20640)

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
      | FStar_Parser_AST.Fsdoc uu____20670 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____20678 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____20678, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____20715  ->
                 match uu____20715 with | (x,uu____20723) -> x) tcs
             in
          let uu____20728 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____20728 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____20750;
                    FStar_Parser_AST.prange = uu____20751;_},uu____20752)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____20761;
                    FStar_Parser_AST.prange = uu____20762;_},uu____20763)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____20778;
                         FStar_Parser_AST.prange = uu____20779;_},uu____20780);
                    FStar_Parser_AST.prange = uu____20781;_},uu____20782)::[]
                   -> false
               | (p,uu____20810)::[] ->
                   let uu____20819 = is_app_pattern p  in
                   Prims.op_Negation uu____20819
               | uu____20820 -> false)
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
            let uu____20893 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____20893 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____20905 =
                     let uu____20906 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____20906.FStar_Syntax_Syntax.n  in
                   match uu____20905 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____20916) ->
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
                         | uu____20949::uu____20950 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____20953 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___110_20968  ->
                                     match uu___110_20968 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____20971;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20972;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20973;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20974;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20975;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20976;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20977;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20989;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20990;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20991;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20992;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20993;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20994;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____21008 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____21039  ->
                                   match uu____21039 with
                                   | (uu____21052,(uu____21053,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____21008
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____21071 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____21071
                         then
                           let uu____21074 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___137_21088 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___138_21090 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___138_21090.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___138_21090.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___137_21088.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___137_21088.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___137_21088.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___137_21088.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___137_21088.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___137_21088.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____21074)
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
                   | uu____21117 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____21123 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____21142 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____21123 with
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
                       let uu___139_21178 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___139_21178.FStar_Parser_AST.prange)
                       }
                   | uu____21185 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___140_21192 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___140_21192.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___140_21192.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___140_21192.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____21228 id1 =
                   match uu____21228 with
                   | (env1,ses) ->
                       let main =
                         let uu____21249 =
                           let uu____21250 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____21250  in
                         FStar_Parser_AST.mk_term uu____21249
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
                       let uu____21300 = desugar_decl env1 id_decl  in
                       (match uu____21300 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____21318 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____21318 FStar_Util.set_elements
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
            let uu____21343 = close_fun env t  in
            desugar_term env uu____21343  in
          let quals1 =
            let uu____21347 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____21347
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____21353 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____21353;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____21361 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____21361 with
           | (t,uu____21375) ->
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
            let uu____21405 =
              let uu____21412 = FStar_Syntax_Syntax.null_binder t  in
              [uu____21412]  in
            let uu____21425 =
              let uu____21426 =
                let uu____21427 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____21427  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____21426
               in
            FStar_Syntax_Util.arrow uu____21405 uu____21425  in
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
            let uu____21486 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____21486 with
            | FStar_Pervasives_Native.None  ->
                let uu____21489 =
                  let uu____21494 =
                    let uu____21495 =
                      let uu____21496 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____21496 " not found"  in
                    Prims.strcat "Effect name " uu____21495  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____21494)  in
                FStar_Errors.raise_error uu____21489
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____21500 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____21518 =
                  let uu____21527 =
                    let uu____21534 = desugar_term env t  in
                    ([], uu____21534)  in
                  FStar_Pervasives_Native.Some uu____21527  in
                (uu____21518, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____21555 =
                  let uu____21564 =
                    let uu____21571 = desugar_term env wp  in
                    ([], uu____21571)  in
                  FStar_Pervasives_Native.Some uu____21564  in
                let uu____21580 =
                  let uu____21589 =
                    let uu____21596 = desugar_term env t  in
                    ([], uu____21596)  in
                  FStar_Pervasives_Native.Some uu____21589  in
                (uu____21555, uu____21580)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____21622 =
                  let uu____21631 =
                    let uu____21638 = desugar_term env t  in
                    ([], uu____21638)  in
                  FStar_Pervasives_Native.Some uu____21631  in
                (FStar_Pervasives_Native.None, uu____21622)
             in
          (match uu____21500 with
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
            let uu____21680 =
              let uu____21681 =
                let uu____21688 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____21688, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____21681  in
            {
              FStar_Syntax_Syntax.sigel = uu____21680;
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
      let uu____21714 =
        FStar_List.fold_left
          (fun uu____21734  ->
             fun d  ->
               match uu____21734 with
               | (env1,sigelts) ->
                   let uu____21754 = desugar_decl env1 d  in
                   (match uu____21754 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____21714 with
      | (env1,sigelts) ->
          let rec forward acc uu___112_21799 =
            match uu___112_21799 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____21813,FStar_Syntax_Syntax.Sig_let uu____21814) ->
                     let uu____21827 =
                       let uu____21830 =
                         let uu___141_21831 = se2  in
                         let uu____21832 =
                           let uu____21835 =
                             FStar_List.filter
                               (fun uu___111_21849  ->
                                  match uu___111_21849 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____21853;
                                           FStar_Syntax_Syntax.vars =
                                             uu____21854;_},uu____21855);
                                      FStar_Syntax_Syntax.pos = uu____21856;
                                      FStar_Syntax_Syntax.vars = uu____21857;_}
                                      when
                                      let uu____21880 =
                                        let uu____21881 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____21881
                                         in
                                      uu____21880 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____21882 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____21835
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___141_21831.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___141_21831.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___141_21831.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___141_21831.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____21832
                         }  in
                       uu____21830 :: se1 :: acc  in
                     forward uu____21827 sigelts1
                 | uu____21887 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____21895 = forward [] sigelts  in (env1, uu____21895)
  
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
      let uu____21937 =
        let uu____21950 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____21967  ->
               match uu____21967 with
               | ({ FStar_Syntax_Syntax.ppname = uu____21976;
                    FStar_Syntax_Syntax.index = uu____21977;
                    FStar_Syntax_Syntax.sort = t;_},uu____21979)
                   ->
                   let uu____21982 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____21982) uu____21950
         in
      FStar_All.pipe_right bs uu____21937  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____21996 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____22013 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____22039 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____22060,uu____22061,bs,t,uu____22064,uu____22065)
                            ->
                            let uu____22074 = bs_univnames bs  in
                            let uu____22077 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____22074 uu____22077
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____22080,uu____22081,t,uu____22083,uu____22084,uu____22085)
                            -> FStar_Syntax_Free.univnames t
                        | uu____22090 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____22039 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___142_22098 = s  in
        let uu____22099 =
          let uu____22100 =
            let uu____22109 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____22127,bs,t,lids1,lids2) ->
                          let uu___143_22140 = se  in
                          let uu____22141 =
                            let uu____22142 =
                              let uu____22159 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____22160 =
                                let uu____22161 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____22161 t  in
                              (lid, uvs, uu____22159, uu____22160, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____22142
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____22141;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___143_22140.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___143_22140.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___143_22140.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___143_22140.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____22173,t,tlid,n1,lids1) ->
                          let uu___144_22182 = se  in
                          let uu____22183 =
                            let uu____22184 =
                              let uu____22199 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____22199, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____22184  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____22183;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___144_22182.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___144_22182.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___144_22182.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___144_22182.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____22202 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____22109, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____22100  in
        {
          FStar_Syntax_Syntax.sigel = uu____22099;
          FStar_Syntax_Syntax.sigrng =
            (uu___142_22098.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___142_22098.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___142_22098.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___142_22098.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22208,t) ->
        let uvs =
          let uu____22211 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____22211 FStar_Util.set_elements  in
        let uu___145_22216 = s  in
        let uu____22217 =
          let uu____22218 =
            let uu____22225 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____22225)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____22218  in
        {
          FStar_Syntax_Syntax.sigel = uu____22217;
          FStar_Syntax_Syntax.sigrng =
            (uu___145_22216.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___145_22216.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___145_22216.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___145_22216.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____22247 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____22250 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____22257) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____22286,(FStar_Util.Inl t,uu____22288),uu____22289)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____22336,(FStar_Util.Inr c,uu____22338),uu____22339)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____22386 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____22387,(FStar_Util.Inl t,uu____22389),uu____22390) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____22437,(FStar_Util.Inr c,uu____22439),uu____22440) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____22487 -> empty_set  in
          FStar_Util.set_union uu____22247 uu____22250  in
        let all_lb_univs =
          let uu____22491 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____22507 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____22507) empty_set)
             in
          FStar_All.pipe_right uu____22491 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___146_22517 = s  in
        let uu____22518 =
          let uu____22519 =
            let uu____22526 =
              let uu____22527 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___147_22539 = lb  in
                        let uu____22540 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____22543 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___147_22539.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____22540;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___147_22539.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____22543;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___147_22539.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___147_22539.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____22527)  in
            (uu____22526, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____22519  in
        {
          FStar_Syntax_Syntax.sigel = uu____22518;
          FStar_Syntax_Syntax.sigrng =
            (uu___146_22517.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___146_22517.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___146_22517.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___146_22517.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____22551,fml) ->
        let uvs =
          let uu____22554 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____22554 FStar_Util.set_elements  in
        let uu___148_22559 = s  in
        let uu____22560 =
          let uu____22561 =
            let uu____22568 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____22568)  in
          FStar_Syntax_Syntax.Sig_assume uu____22561  in
        {
          FStar_Syntax_Syntax.sigel = uu____22560;
          FStar_Syntax_Syntax.sigrng =
            (uu___148_22559.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___148_22559.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___148_22559.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___148_22559.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____22570,bs,c,flags1) ->
        let uvs =
          let uu____22579 =
            let uu____22582 = bs_univnames bs  in
            let uu____22585 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____22582 uu____22585  in
          FStar_All.pipe_right uu____22579 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___149_22593 = s  in
        let uu____22594 =
          let uu____22595 =
            let uu____22608 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____22609 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____22608, uu____22609, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____22595  in
        {
          FStar_Syntax_Syntax.sigel = uu____22594;
          FStar_Syntax_Syntax.sigrng =
            (uu___149_22593.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___149_22593.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___149_22593.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___149_22593.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____22612 -> s
  
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
          | (FStar_Pervasives_Native.None ,uu____22647) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____22651;
               FStar_Syntax_Syntax.exports = uu____22652;
               FStar_Syntax_Syntax.is_interface = uu____22653;_},FStar_Parser_AST.Module
             (current_lid,uu____22655)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____22663) ->
              let uu____22666 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____22666
           in
        let uu____22671 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____22707 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____22707, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____22724 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____22724, mname, decls, false)
           in
        match uu____22671 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____22754 = desugar_decls env2 decls  in
            (match uu____22754 with
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
          let uu____22819 =
            (FStar_Options.interactive ()) &&
              (let uu____22821 =
                 let uu____22822 =
                   let uu____22823 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____22823  in
                 FStar_Util.get_file_extension uu____22822  in
               FStar_List.mem uu____22821 ["fsti"; "fsi"])
             in
          if uu____22819 then as_interface m else m  in
        let uu____22827 = desugar_modul_common curmod env m1  in
        match uu____22827 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____22842 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____22862 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____22862 with
      | (env1,modul,pop_when_done) ->
          let uu____22876 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____22876 with
           | (env2,modul1) ->
               ((let uu____22888 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____22888
                 then
                   let uu____22889 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____22889
                 else ());
                (let uu____22891 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____22891, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____22909 = desugar_modul env modul  in
      match uu____22909 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____22940 = desugar_decls env decls  in
      match uu____22940 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____22982 = desugar_partial_modul modul env a_modul  in
        match uu____22982 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____23068 ->
                  let t =
                    let uu____23076 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____23076  in
                  let uu____23087 =
                    let uu____23088 = FStar_Syntax_Subst.compress t  in
                    uu____23088.FStar_Syntax_Syntax.n  in
                  (match uu____23087 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____23098,uu____23099)
                       -> bs1
                   | uu____23120 -> failwith "Impossible")
               in
            let uu____23127 =
              let uu____23134 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____23134
                FStar_Syntax_Syntax.t_unit
               in
            match uu____23127 with
            | (binders,uu____23136,binders_opening) ->
                let erase_term t =
                  let uu____23144 =
                    let uu____23145 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____23145  in
                  FStar_Syntax_Subst.close binders uu____23144  in
                let erase_tscheme uu____23163 =
                  match uu____23163 with
                  | (us,t) ->
                      let t1 =
                        let uu____23183 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____23183 t  in
                      let uu____23186 =
                        let uu____23187 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____23187  in
                      ([], uu____23186)
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
                    | uu____23206 ->
                        let bs =
                          let uu____23214 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____23214  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____23246 =
                          let uu____23247 =
                            let uu____23250 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____23250  in
                          uu____23247.FStar_Syntax_Syntax.n  in
                        (match uu____23246 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____23252,uu____23253) -> bs1
                         | uu____23274 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____23281 =
                      let uu____23282 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____23282  in
                    FStar_Syntax_Subst.close binders uu____23281  in
                  let uu___150_23283 = action  in
                  let uu____23284 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____23285 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___150_23283.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___150_23283.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____23284;
                    FStar_Syntax_Syntax.action_typ = uu____23285
                  }  in
                let uu___151_23286 = ed  in
                let uu____23287 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____23288 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____23289 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____23290 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____23291 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____23292 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____23293 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____23294 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____23295 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____23296 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____23297 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____23298 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____23299 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____23300 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____23301 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____23302 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___151_23286.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___151_23286.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____23287;
                  FStar_Syntax_Syntax.signature = uu____23288;
                  FStar_Syntax_Syntax.ret_wp = uu____23289;
                  FStar_Syntax_Syntax.bind_wp = uu____23290;
                  FStar_Syntax_Syntax.if_then_else = uu____23291;
                  FStar_Syntax_Syntax.ite_wp = uu____23292;
                  FStar_Syntax_Syntax.stronger = uu____23293;
                  FStar_Syntax_Syntax.close_wp = uu____23294;
                  FStar_Syntax_Syntax.assert_p = uu____23295;
                  FStar_Syntax_Syntax.assume_p = uu____23296;
                  FStar_Syntax_Syntax.null_wp = uu____23297;
                  FStar_Syntax_Syntax.trivial = uu____23298;
                  FStar_Syntax_Syntax.repr = uu____23299;
                  FStar_Syntax_Syntax.return_repr = uu____23300;
                  FStar_Syntax_Syntax.bind_repr = uu____23301;
                  FStar_Syntax_Syntax.actions = uu____23302;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___151_23286.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___152_23318 = se  in
                  let uu____23319 =
                    let uu____23320 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____23320  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____23319;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___152_23318.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___152_23318.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___152_23318.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___152_23318.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___153_23324 = se  in
                  let uu____23325 =
                    let uu____23326 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____23326
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____23325;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___153_23324.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___153_23324.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___153_23324.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___153_23324.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____23328 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____23329 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____23329 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____23341 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____23341
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____23343 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____23343)
  