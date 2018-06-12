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
  fun uu___230_66  ->
    match uu___230_66 with
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
      fun uu___231_90  ->
        match uu___231_90 with
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
  fun uu___232_99  ->
    match uu___232_99 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___233_110  ->
    match uu___233_110 with
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
  fun uu___234_1708  ->
    match uu___234_1708 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1715 -> failwith "Impossible"
  
let (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term'
                                                          FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple2 ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2,FStar_Syntax_DsEnv.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun imp  ->
      fun uu___235_1752  ->
        match uu___235_1752 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1778 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1778, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1795 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1795 with
             | (env1,a1) ->
                 (((let uu___259_1815 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___259_1815.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___259_1815.FStar_Syntax_Syntax.index);
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
  fun uu____1844  ->
    match uu____1844 with
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
      let uu____1924 =
        let uu____1939 =
          let uu____1942 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1942  in
        let uu____1943 =
          let uu____1952 =
            let uu____1959 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1959)  in
          [uu____1952]  in
        (uu____1939, uu____1943)  in
      FStar_Syntax_Syntax.Tm_app uu____1924  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1996 =
        let uu____2011 =
          let uu____2014 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2014  in
        let uu____2015 =
          let uu____2024 =
            let uu____2031 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2031)  in
          [uu____2024]  in
        (uu____2011, uu____2015)  in
      FStar_Syntax_Syntax.Tm_app uu____1996  in
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
          let uu____2082 =
            let uu____2097 =
              let uu____2100 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2100  in
            let uu____2101 =
              let uu____2110 =
                let uu____2117 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2117)  in
              let uu____2120 =
                let uu____2129 =
                  let uu____2136 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2136)  in
                [uu____2129]  in
              uu____2110 :: uu____2120  in
            (uu____2097, uu____2101)  in
          FStar_Syntax_Syntax.Tm_app uu____2082  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2182 =
        let uu____2195 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2212  ->
               match uu____2212 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2221;
                    FStar_Syntax_Syntax.index = uu____2222;
                    FStar_Syntax_Syntax.sort = t;_},uu____2224)
                   ->
                   let uu____2227 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2227) uu____2195
         in
      FStar_All.pipe_right bs uu____2182  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2241 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2258 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2284 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2305,uu____2306,bs,t,uu____2309,uu____2310)
                            ->
                            let uu____2319 = bs_univnames bs  in
                            let uu____2322 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2319 uu____2322
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2325,uu____2326,t,uu____2328,uu____2329,uu____2330)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2335 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2284 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___260_2343 = s  in
        let uu____2344 =
          let uu____2345 =
            let uu____2354 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2372,bs,t,lids1,lids2) ->
                          let uu___261_2385 = se  in
                          let uu____2386 =
                            let uu____2387 =
                              let uu____2404 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2405 =
                                let uu____2406 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2406 t  in
                              (lid, uvs, uu____2404, uu____2405, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2387
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2386;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___261_2385.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___261_2385.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___261_2385.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___261_2385.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2418,t,tlid,n1,lids1) ->
                          let uu___262_2427 = se  in
                          let uu____2428 =
                            let uu____2429 =
                              let uu____2444 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2444, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2429  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2428;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___262_2427.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___262_2427.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___262_2427.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___262_2427.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2447 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2354, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2345  in
        {
          FStar_Syntax_Syntax.sigel = uu____2344;
          FStar_Syntax_Syntax.sigrng =
            (uu___260_2343.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___260_2343.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___260_2343.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___260_2343.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2453,t) ->
        let uvs =
          let uu____2456 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2456 FStar_Util.set_elements  in
        let uu___263_2461 = s  in
        let uu____2462 =
          let uu____2463 =
            let uu____2470 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2470)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2463  in
        {
          FStar_Syntax_Syntax.sigel = uu____2462;
          FStar_Syntax_Syntax.sigrng =
            (uu___263_2461.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___263_2461.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___263_2461.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___263_2461.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2492 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2495 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2502) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2531,(FStar_Util.Inl t,uu____2533),uu____2534)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2581,(FStar_Util.Inr c,uu____2583),uu____2584)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2631 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2632,(FStar_Util.Inl t,uu____2634),uu____2635) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2682,(FStar_Util.Inr c,uu____2684),uu____2685) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2732 -> empty_set  in
          FStar_Util.set_union uu____2492 uu____2495  in
        let all_lb_univs =
          let uu____2736 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2752 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2752) empty_set)
             in
          FStar_All.pipe_right uu____2736 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___264_2762 = s  in
        let uu____2763 =
          let uu____2764 =
            let uu____2771 =
              let uu____2772 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___265_2784 = lb  in
                        let uu____2785 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2788 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___265_2784.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2785;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___265_2784.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2788;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___265_2784.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___265_2784.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2772)  in
            (uu____2771, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2764  in
        {
          FStar_Syntax_Syntax.sigel = uu____2763;
          FStar_Syntax_Syntax.sigrng =
            (uu___264_2762.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___264_2762.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___264_2762.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___264_2762.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2796,fml) ->
        let uvs =
          let uu____2799 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2799 FStar_Util.set_elements  in
        let uu___266_2804 = s  in
        let uu____2805 =
          let uu____2806 =
            let uu____2813 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2813)  in
          FStar_Syntax_Syntax.Sig_assume uu____2806  in
        {
          FStar_Syntax_Syntax.sigel = uu____2805;
          FStar_Syntax_Syntax.sigrng =
            (uu___266_2804.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___266_2804.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___266_2804.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___266_2804.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2815,bs,c,flags1) ->
        let uvs =
          let uu____2824 =
            let uu____2827 = bs_univnames bs  in
            let uu____2830 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2827 uu____2830  in
          FStar_All.pipe_right uu____2824 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___267_2838 = s  in
        let uu____2839 =
          let uu____2840 =
            let uu____2853 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____2854 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2853, uu____2854, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2840  in
        {
          FStar_Syntax_Syntax.sigel = uu____2839;
          FStar_Syntax_Syntax.sigrng =
            (uu___267_2838.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___267_2838.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___267_2838.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___267_2838.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____2857 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___236_2862  ->
    match uu___236_2862 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2863 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2875 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2875)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2894 =
      let uu____2895 = unparen t  in uu____2895.FStar_Parser_AST.tm  in
    match uu____2894 with
    | FStar_Parser_AST.Wild  ->
        let uu____2900 =
          let uu____2901 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2901  in
        FStar_Util.Inr uu____2900
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2912)) ->
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
             let uu____2977 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2977
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2988 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2988
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2999 =
               let uu____3004 =
                 let uu____3005 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3005
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3004)
                in
             FStar_Errors.raise_error uu____2999 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3010 ->
        let rec aux t1 univargs =
          let uu____3044 =
            let uu____3045 = unparen t1  in uu____3045.FStar_Parser_AST.tm
             in
          match uu____3044 with
          | FStar_Parser_AST.App (t2,targ,uu____3052) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___237_3075  ->
                     match uu___237_3075 with
                     | FStar_Util.Inr uu____3080 -> true
                     | uu____3081 -> false) univargs
              then
                let uu____3086 =
                  let uu____3087 =
                    FStar_List.map
                      (fun uu___238_3096  ->
                         match uu___238_3096 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3087  in
                FStar_Util.Inr uu____3086
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___239_3113  ->
                        match uu___239_3113 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3119 -> failwith "impossible")
                     univargs
                    in
                 let uu____3120 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3120)
          | uu____3126 ->
              let uu____3127 =
                let uu____3132 =
                  let uu____3133 =
                    let uu____3134 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3134 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3133  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3132)  in
              FStar_Errors.raise_error uu____3127 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3143 ->
        let uu____3144 =
          let uu____3149 =
            let uu____3150 =
              let uu____3151 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3151 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3150  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3149)  in
        FStar_Errors.raise_error uu____3144 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____3184 ->
        let uu____3207 =
          let uu____3212 =
            let uu____3213 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____3213
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3212)  in
        FStar_Errors.raise_error uu____3207 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3223 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3223) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3251 = FStar_List.hd fields  in
        match uu____3251 with
        | (f,uu____3261) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3273 =
                match uu____3273 with
                | (f',uu____3279) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3281 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3281
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
              (let uu____3285 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3285);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____3636 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____3643 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____3644 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____3646,pats1) ->
                let aux out uu____3684 =
                  match uu____3684 with
                  | (p2,uu____3696) ->
                      let intersection =
                        let uu____3704 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3704 out  in
                      let uu____3707 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3707
                      then
                        let uu____3710 = pat_vars p2  in
                        FStar_Util.set_union out uu____3710
                      else
                        (let duplicate_bv =
                           let uu____3715 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3715  in
                         let uu____3718 =
                           let uu____3723 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3723)
                            in
                         FStar_Errors.raise_error uu____3718 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3743 = pat_vars p1  in
              FStar_All.pipe_right uu____3743 (fun a237  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3771 =
                  let uu____3772 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3772  in
                if uu____3771
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3779 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3779  in
                   let first_nonlinear_var =
                     let uu____3783 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3783  in
                   let uu____3786 =
                     let uu____3791 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3791)  in
                   FStar_Errors.raise_error uu____3786 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3795) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3796) -> ()
         | (true ,uu____3803) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3826 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____3826 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3842 ->
               let uu____3845 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____3845 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3957 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____3973 =
                 let uu____3974 =
                   let uu____3975 =
                     let uu____3982 =
                       let uu____3983 =
                         let uu____3988 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____3988, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____3983  in
                     (uu____3982, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____3975  in
                 {
                   FStar_Parser_AST.pat = uu____3974;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____3973
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____4005 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____4006 = aux loc env1 p2  in
                 match uu____4006 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___268_4064 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___269_4069 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___269_4069.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___269_4069.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___268_4064.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___270_4071 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___271_4076 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___271_4076.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___271_4076.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___270_4071.FStar_Syntax_Syntax.p)
                           }
                       | uu____4077 when top -> p4
                       | uu____4078 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____4081 =
                       match binder with
                       | LetBinder uu____4094 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____4114 = close_fun env1 t  in
                             desugar_term env1 uu____4114  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____4116 -> true)
                            then
                              (let uu____4117 =
                                 let uu____4122 =
                                   let uu____4123 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____4124 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____4125 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____4123 uu____4124 uu____4125
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____4122)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____4117)
                            else ();
                            (let uu____4127 = annot_pat_var p3 t1  in
                             (uu____4127,
                               (LocalBinder
                                  ((let uu___272_4133 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___272_4133.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___272_4133.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____4081 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4155 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4155, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4164 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4164, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____4183 = resolvex loc env1 x  in
               (match uu____4183 with
                | (loc1,env2,xbv) ->
                    let uu____4205 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4205, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____4224 = resolvex loc env1 x  in
               (match uu____4224 with
                | (loc1,env2,xbv) ->
                    let uu____4246 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4246, imp))
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
               let uu____4256 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4256, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____4278;_},args)
               ->
               let uu____4284 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____4325  ->
                        match uu____4325 with
                        | (loc1,env2,args1) ->
                            let uu____4373 = aux loc1 env2 arg  in
                            (match uu____4373 with
                             | (loc2,env3,uu____4402,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____4284 with
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
                    let uu____4472 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____4472, false))
           | FStar_Parser_AST.PatApp uu____4487 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____4509 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____4542  ->
                        match uu____4542 with
                        | (loc1,env2,pats1) ->
                            let uu____4574 = aux loc1 env2 pat  in
                            (match uu____4574 with
                             | (loc2,env3,uu____4599,pat1,uu____4601) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____4509 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____4644 =
                        let uu____4647 =
                          let uu____4654 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____4654  in
                        let uu____4655 =
                          let uu____4656 =
                            let uu____4669 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____4669, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____4656  in
                        FStar_All.pipe_left uu____4647 uu____4655  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____4701 =
                               let uu____4702 =
                                 let uu____4715 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____4715, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____4702  in
                             FStar_All.pipe_left (pos_r r) uu____4701) pats1
                        uu____4644
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
               let uu____4757 =
                 FStar_List.fold_left
                   (fun uu____4797  ->
                      fun p2  ->
                        match uu____4797 with
                        | (loc1,env2,pats) ->
                            let uu____4846 = aux loc1 env2 p2  in
                            (match uu____4846 with
                             | (loc2,env3,uu____4875,pat,uu____4877) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4757 with
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
                    let uu____4972 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____4972 with
                     | (constr,uu____4994) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____4997 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____4999 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____4999, false)))
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
                      (fun uu____5068  ->
                         match uu____5068 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____5098  ->
                         match uu____5098 with
                         | (f,uu____5104) ->
                             let uu____5105 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____5131  ->
                                       match uu____5131 with
                                       | (g,uu____5137) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____5105 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____5142,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____5149 =
                   let uu____5150 =
                     let uu____5157 =
                       let uu____5158 =
                         let uu____5159 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____5159  in
                       FStar_Parser_AST.mk_pattern uu____5158
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____5157, args)  in
                   FStar_Parser_AST.PatApp uu____5150  in
                 FStar_Parser_AST.mk_pattern uu____5149
                   p1.FStar_Parser_AST.prange
                  in
               let uu____5162 = aux loc env1 app  in
               (match uu____5162 with
                | (env2,e,b,p2,uu____5191) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____5219 =
                            let uu____5220 =
                              let uu____5233 =
                                let uu___273_5234 = fv  in
                                let uu____5235 =
                                  let uu____5238 =
                                    let uu____5239 =
                                      let uu____5246 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____5246)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____5239
                                     in
                                  FStar_Pervasives_Native.Some uu____5238  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___273_5234.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___273_5234.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____5235
                                }  in
                              (uu____5233, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____5220  in
                          FStar_All.pipe_left pos uu____5219
                      | uu____5273 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____5327 = aux' true loc env1 p2  in
               (match uu____5327 with
                | (loc1,env2,var,p3,uu____5354) ->
                    let uu____5359 =
                      FStar_List.fold_left
                        (fun uu____5391  ->
                           fun p4  ->
                             match uu____5391 with
                             | (loc2,env3,ps1) ->
                                 let uu____5424 = aux' true loc2 env3 p4  in
                                 (match uu____5424 with
                                  | (loc3,env4,uu____5449,p5,uu____5451) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____5359 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____5502 ->
               let uu____5503 = aux' true loc env1 p1  in
               (match uu____5503 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____5543 = aux_maybe_or env p  in
         match uu____5543 with
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
            let uu____5602 =
              let uu____5603 =
                let uu____5614 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____5614,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____5603  in
            (env, uu____5602, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____5642 =
                  let uu____5643 =
                    let uu____5648 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____5648, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____5643  in
                mklet uu____5642
            | FStar_Parser_AST.PatVar (x,uu____5650) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____5656);
                   FStar_Parser_AST.prange = uu____5657;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____5677 =
                  let uu____5678 =
                    let uu____5689 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____5690 =
                      let uu____5697 = desugar_term env t  in
                      (uu____5697, tacopt1)  in
                    (uu____5689, uu____5690)  in
                  LetBinder uu____5678  in
                (env, uu____5677, [])
            | uu____5708 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5718 = desugar_data_pat env p is_mut  in
             match uu____5718 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5747;
                       FStar_Syntax_Syntax.p = uu____5748;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5749;
                       FStar_Syntax_Syntax.p = uu____5750;_}::[] -> []
                   | uu____5751 -> p1  in
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
  fun uu____5758  ->
    fun env  ->
      fun pat  ->
        let uu____5761 = desugar_data_pat env pat false  in
        match uu____5761 with | (env1,uu____5777,pat1) -> (env1, pat1)

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
      let uu____5796 = desugar_term_aq env e  in
      match uu____5796 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____5813 = desugar_typ_aq env e  in
      match uu____5813 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5823  ->
        fun range  ->
          match uu____5823 with
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
              ((let uu____5833 =
                  let uu____5834 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5834  in
                if uu____5833
                then
                  let uu____5835 =
                    let uu____5840 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5840)  in
                  FStar_Errors.log_issue range uu____5835
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
                  let uu____5845 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____5845 range  in
                let lid1 =
                  let uu____5849 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____5849 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____5859) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5868 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____5868 range  in
                           let private_fv =
                             let uu____5870 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5870 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___274_5871 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___274_5871.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___274_5871.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5872 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5879 =
                        let uu____5884 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5884)
                         in
                      FStar_Errors.raise_error uu____5879 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____5900 =
                  let uu____5907 =
                    let uu____5908 =
                      let uu____5923 =
                        let uu____5932 =
                          let uu____5939 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____5939)  in
                        [uu____5932]  in
                      (lid1, uu____5923)  in
                    FStar_Syntax_Syntax.Tm_app uu____5908  in
                  FStar_Syntax_Syntax.mk uu____5907  in
                uu____5900 FStar_Pervasives_Native.None range))

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
            let uu____5978 =
              let uu____5987 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____5987 l  in
            match uu____5978 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____6042;
                              FStar_Syntax_Syntax.vars = uu____6043;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6066 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6066 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____6074 =
                                 let uu____6075 =
                                   let uu____6078 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____6078  in
                                 uu____6075.FStar_Syntax_Syntax.n  in
                               match uu____6074 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____6094))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____6095 -> msg
                             else msg  in
                           let uu____6097 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6097
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6100 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6100 " is deprecated"  in
                           let uu____6101 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6101
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____6102 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____6107 =
                      let uu____6108 =
                        let uu____6115 = mk_ref_read tm1  in
                        (uu____6115,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____6108  in
                    FStar_All.pipe_left mk1 uu____6107
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____6133 =
          let uu____6134 = unparen t  in uu____6134.FStar_Parser_AST.tm  in
        match uu____6133 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____6135; FStar_Ident.ident = uu____6136;
              FStar_Ident.nsstr = uu____6137; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____6140 ->
            let uu____6141 =
              let uu____6146 =
                let uu____6147 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____6147  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____6146)  in
            FStar_Errors.raise_error uu____6141 t.FStar_Parser_AST.range
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
          let uu___275_6242 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___275_6242.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___275_6242.FStar_Syntax_Syntax.vars)
          }  in
        let uu____6245 =
          let uu____6246 = unparen top  in uu____6246.FStar_Parser_AST.tm  in
        match uu____6245 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____6251 ->
            let uu____6258 = desugar_formula env top  in (uu____6258, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____6265 = desugar_formula env t  in (uu____6265, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____6272 = desugar_formula env t  in (uu____6272, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____6296 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____6296, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____6298 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____6298, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____6306 =
                let uu____6307 =
                  let uu____6314 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____6314, args)  in
                FStar_Parser_AST.Op uu____6307  in
              FStar_Parser_AST.mk_term uu____6306 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____6317 =
              let uu____6318 =
                let uu____6319 =
                  let uu____6326 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____6326, [e])  in
                FStar_Parser_AST.Op uu____6319  in
              FStar_Parser_AST.mk_term uu____6318 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____6317
        | FStar_Parser_AST.Op (op_star,uu____6330::uu____6331::[]) when
            (let uu____6336 = FStar_Ident.text_of_id op_star  in
             uu____6336 = "*") &&
              (let uu____6338 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____6338 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____6353;_},t1::t2::[])
                  ->
                  let uu____6358 = flatten1 t1  in
                  FStar_List.append uu____6358 [t2]
              | uu____6361 -> [t]  in
            let uu____6362 =
              let uu____6387 =
                let uu____6410 =
                  let uu____6413 = unparen top  in flatten1 uu____6413  in
                FStar_All.pipe_right uu____6410
                  (FStar_List.map
                     (fun t  ->
                        let uu____6448 = desugar_typ_aq env t  in
                        match uu____6448 with
                        | (t',aq) ->
                            let uu____6459 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____6459, aq)))
                 in
              FStar_All.pipe_right uu____6387 FStar_List.unzip  in
            (match uu____6362 with
             | (targs,aqs) ->
                 let uu____6568 =
                   let uu____6573 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____6573
                    in
                 (match uu____6568 with
                  | (tup,uu____6589) ->
                      let uu____6590 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____6590, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____6602 =
              let uu____6603 =
                let uu____6606 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____6606  in
              FStar_All.pipe_left setpos uu____6603  in
            (uu____6602, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____6618 =
              let uu____6623 =
                let uu____6624 =
                  let uu____6625 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____6625 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____6624  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____6623)  in
            FStar_Errors.raise_error uu____6618 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____6636 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____6636 with
             | FStar_Pervasives_Native.None  ->
                 let uu____6643 =
                   let uu____6648 =
                     let uu____6649 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____6649
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____6648)
                    in
                 FStar_Errors.raise_error uu____6643
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____6659 =
                     let uu____6684 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____6746 = desugar_term_aq env t  in
                               match uu____6746 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____6684 FStar_List.unzip  in
                   (match uu____6659 with
                    | (args1,aqs) ->
                        let uu____6879 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6879, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6893)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6908 =
              let uu___276_6909 = top  in
              let uu____6910 =
                let uu____6911 =
                  let uu____6918 =
                    let uu___277_6919 = top  in
                    let uu____6920 =
                      let uu____6921 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6921  in
                    {
                      FStar_Parser_AST.tm = uu____6920;
                      FStar_Parser_AST.range =
                        (uu___277_6919.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___277_6919.FStar_Parser_AST.level)
                    }  in
                  (uu____6918, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6911  in
              {
                FStar_Parser_AST.tm = uu____6910;
                FStar_Parser_AST.range =
                  (uu___276_6909.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___276_6909.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6908
        | FStar_Parser_AST.Construct (n1,(a,uu____6924)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6940 =
                let uu___278_6941 = top  in
                let uu____6942 =
                  let uu____6943 =
                    let uu____6950 =
                      let uu___279_6951 = top  in
                      let uu____6952 =
                        let uu____6953 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____6953  in
                      {
                        FStar_Parser_AST.tm = uu____6952;
                        FStar_Parser_AST.range =
                          (uu___279_6951.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___279_6951.FStar_Parser_AST.level)
                      }  in
                    (uu____6950, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____6943  in
                {
                  FStar_Parser_AST.tm = uu____6942;
                  FStar_Parser_AST.range =
                    (uu___278_6941.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___278_6941.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____6940))
        | FStar_Parser_AST.Construct (n1,(a,uu____6956)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6971 =
              let uu___280_6972 = top  in
              let uu____6973 =
                let uu____6974 =
                  let uu____6981 =
                    let uu___281_6982 = top  in
                    let uu____6983 =
                      let uu____6984 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6984  in
                    {
                      FStar_Parser_AST.tm = uu____6983;
                      FStar_Parser_AST.range =
                        (uu___281_6982.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___281_6982.FStar_Parser_AST.level)
                    }  in
                  (uu____6981, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6974  in
              {
                FStar_Parser_AST.tm = uu____6973;
                FStar_Parser_AST.range =
                  (uu___280_6972.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___280_6972.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6971
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6985; FStar_Ident.ident = uu____6986;
              FStar_Ident.nsstr = uu____6987; FStar_Ident.str = "Type0";_}
            ->
            let uu____6990 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____6990, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6991; FStar_Ident.ident = uu____6992;
              FStar_Ident.nsstr = uu____6993; FStar_Ident.str = "Type";_}
            ->
            let uu____6996 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____6996, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6997; FStar_Ident.ident = uu____6998;
               FStar_Ident.nsstr = uu____6999; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____7017 =
              let uu____7018 =
                let uu____7019 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____7019  in
              mk1 uu____7018  in
            (uu____7017, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7020; FStar_Ident.ident = uu____7021;
              FStar_Ident.nsstr = uu____7022; FStar_Ident.str = "Effect";_}
            ->
            let uu____7025 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____7025, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7026; FStar_Ident.ident = uu____7027;
              FStar_Ident.nsstr = uu____7028; FStar_Ident.str = "True";_}
            ->
            let uu____7031 =
              let uu____7032 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7032
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7031, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7033; FStar_Ident.ident = uu____7034;
              FStar_Ident.nsstr = uu____7035; FStar_Ident.str = "False";_}
            ->
            let uu____7038 =
              let uu____7039 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7039
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7038, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____7042;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____7044 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____7044 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____7053 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____7053, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____7054 =
                    let uu____7055 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____7055 txt
                     in
                  failwith uu____7054))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7062 = desugar_name mk1 setpos env true l  in
              (uu____7062, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7065 = desugar_name mk1 setpos env true l  in
              (uu____7065, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____7076 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____7076 with
                | FStar_Pervasives_Native.Some uu____7085 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____7090 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____7090 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____7104 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____7121 =
                    let uu____7122 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____7122  in
                  (uu____7121, noaqs)
              | uu____7123 ->
                  let uu____7130 =
                    let uu____7135 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____7135)  in
                  FStar_Errors.raise_error uu____7130
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____7142 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____7142 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7149 =
                    let uu____7154 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____7154)
                     in
                  FStar_Errors.raise_error uu____7149
                    top.FStar_Parser_AST.range
              | uu____7159 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____7163 = desugar_name mk1 setpos env true lid'  in
                  (uu____7163, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7179 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____7179 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____7198 ->
                       let uu____7205 =
                         FStar_Util.take
                           (fun uu____7229  ->
                              match uu____7229 with
                              | (uu____7234,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____7205 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____7279 =
                              let uu____7304 =
                                FStar_List.map
                                  (fun uu____7347  ->
                                     match uu____7347 with
                                     | (t,imp) ->
                                         let uu____7364 =
                                           desugar_term_aq env t  in
                                         (match uu____7364 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____7304
                                FStar_List.unzip
                               in
                            (match uu____7279 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____7505 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____7505, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____7521 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____7521 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____7528 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____7539 =
              FStar_List.fold_left
                (fun uu____7580  ->
                   fun b  ->
                     match uu____7580 with
                     | (env1,tparams,typs) ->
                         let uu____7629 = desugar_binder env1 b  in
                         (match uu____7629 with
                          | (xopt,t1) ->
                              let uu____7656 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____7665 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____7665)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____7656 with
                               | (env2,x) ->
                                   let uu____7683 =
                                     let uu____7686 =
                                       let uu____7689 =
                                         let uu____7690 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7690
                                          in
                                       [uu____7689]  in
                                     FStar_List.append typs uu____7686  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___282_7708 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___282_7708.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___282_7708.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____7683)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____7539 with
             | (env1,uu____7730,targs) ->
                 let uu____7748 =
                   let uu____7753 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7753
                    in
                 (match uu____7748 with
                  | (tup,uu____7763) ->
                      let uu____7764 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7764, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7781 = uncurry binders t  in
            (match uu____7781 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___240_7823 =
                   match uu___240_7823 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7837 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7837
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7859 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7859 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7884 = aux env [] bs  in (uu____7884, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7891 = desugar_binder env b  in
            (match uu____7891 with
             | (FStar_Pervasives_Native.None ,uu____7902) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7916 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____7916 with
                  | ((x,uu____7930),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____7937 =
                        let uu____7938 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____7938  in
                      (uu____7937, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____7956 =
              FStar_List.fold_left
                (fun uu____7976  ->
                   fun pat  ->
                     match uu____7976 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____8002,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____8012 =
                                let uu____8015 = free_type_vars env1 t  in
                                FStar_List.append uu____8015 ftvs  in
                              (env1, uu____8012)
                          | FStar_Parser_AST.PatAscribed
                              (uu____8020,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____8031 =
                                let uu____8034 = free_type_vars env1 t  in
                                let uu____8037 =
                                  let uu____8040 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____8040 ftvs  in
                                FStar_List.append uu____8034 uu____8037  in
                              (env1, uu____8031)
                          | uu____8045 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____7956 with
             | (uu____8054,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____8066 =
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
                   FStar_List.append uu____8066 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___241_8121 =
                   match uu___241_8121 with
                   | [] ->
                       let uu____8146 = desugar_term_aq env1 body  in
                       (match uu____8146 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____8183 =
                                      let uu____8184 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____8184
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____8183 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____8253 =
                              let uu____8256 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____8256  in
                            (uu____8253, aq))
                   | p::rest ->
                       let uu____8269 = desugar_binding_pat env1 p  in
                       (match uu____8269 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____8305 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____8312 =
                              match b with
                              | LetBinder uu____8349 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____8415) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____8469 =
                                          let uu____8478 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____8478, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____8469
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____8540,uu____8541) ->
                                             let tup2 =
                                               let uu____8543 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8543
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8547 =
                                                 let uu____8554 =
                                                   let uu____8555 =
                                                     let uu____8570 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____8573 =
                                                       let uu____8582 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____8589 =
                                                         let uu____8598 =
                                                           let uu____8605 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____8605
                                                            in
                                                         [uu____8598]  in
                                                       uu____8582 ::
                                                         uu____8589
                                                        in
                                                     (uu____8570, uu____8573)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8555
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8554
                                                  in
                                               uu____8547
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____8646 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____8646
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____8689,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____8691,pats)) ->
                                             let tupn =
                                               let uu____8730 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8730
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8740 =
                                                 let uu____8741 =
                                                   let uu____8756 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____8759 =
                                                     let uu____8768 =
                                                       let uu____8777 =
                                                         let uu____8784 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____8784
                                                          in
                                                       [uu____8777]  in
                                                     FStar_List.append args
                                                       uu____8768
                                                      in
                                                   (uu____8756, uu____8759)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8741
                                                  in
                                               mk1 uu____8740  in
                                             let p2 =
                                               let uu____8822 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____8822
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____8863 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____8312 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____8944,uu____8945,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____8967 =
                let uu____8968 = unparen e  in uu____8968.FStar_Parser_AST.tm
                 in
              match uu____8967 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____8978 ->
                  let uu____8979 = desugar_term_aq env e  in
                  (match uu____8979 with
                   | (head1,aq) ->
                       let uu____8992 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____8992, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____8999 ->
            let rec aux args aqs e =
              let uu____9078 =
                let uu____9079 = unparen e  in uu____9079.FStar_Parser_AST.tm
                 in
              match uu____9078 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____9099 = desugar_term_aq env t  in
                  (match uu____9099 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____9149 ->
                  let uu____9150 = desugar_term_aq env e  in
                  (match uu____9150 with
                   | (head1,aq) ->
                       let uu____9173 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____9173, (join_aqs (aq :: aqs))))
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
            let uu____9235 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____9235
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
            let uu____9287 = desugar_term_aq env t  in
            (match uu____9287 with
             | (tm,s) ->
                 let uu____9298 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____9298, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____9304 =
              let uu____9317 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____9317 then desugar_typ_aq else desugar_term_aq  in
            uu____9304 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____9372 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____9515  ->
                        match uu____9515 with
                        | (attr_opt,(p,def)) ->
                            let uu____9573 = is_app_pattern p  in
                            if uu____9573
                            then
                              let uu____9604 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____9604, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____9686 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____9686, def1)
                               | uu____9731 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____9769);
                                           FStar_Parser_AST.prange =
                                             uu____9770;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____9818 =
                                            let uu____9839 =
                                              let uu____9844 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9844  in
                                            (uu____9839, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____9818, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____9935) ->
                                        if top_level
                                        then
                                          let uu____9970 =
                                            let uu____9991 =
                                              let uu____9996 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9996  in
                                            (uu____9991, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____9970, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____10086 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____10117 =
                FStar_List.fold_left
                  (fun uu____10190  ->
                     fun uu____10191  ->
                       match (uu____10190, uu____10191) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____10299,uu____10300),uu____10301))
                           ->
                           let uu____10418 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____10444 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____10444 with
                                  | (env2,xx) ->
                                      let uu____10463 =
                                        let uu____10466 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____10466 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____10463))
                             | FStar_Util.Inr l ->
                                 let uu____10474 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____10474, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____10418 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____10117 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____10622 =
                    match uu____10622 with
                    | (attrs_opt,(uu____10658,args,result_t),def) ->
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
                                let uu____10746 = is_comp_type env1 t  in
                                if uu____10746
                                then
                                  ((let uu____10748 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____10758 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____10758))
                                       in
                                    match uu____10748 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____10761 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____10763 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____10763))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____10761
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
                          | uu____10770 ->
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
                              let uu____10785 =
                                let uu____10786 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____10786
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____10785
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
                  let uu____10863 = desugar_term_aq env' body  in
                  (match uu____10863 with
                   | (body1,aq) ->
                       let uu____10876 =
                         let uu____10879 =
                           let uu____10880 =
                             let uu____10893 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____10893)  in
                           FStar_Syntax_Syntax.Tm_let uu____10880  in
                         FStar_All.pipe_left mk1 uu____10879  in
                       (uu____10876, aq))
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
              let uu____10973 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____10973 with
              | (env1,binder,pat1) ->
                  let uu____10995 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____11021 = desugar_term_aq env1 t2  in
                        (match uu____11021 with
                         | (body1,aq) ->
                             let fv =
                               let uu____11035 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____11035
                                 FStar_Pervasives_Native.None
                                in
                             let uu____11036 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____11036, aq))
                    | LocalBinder (x,uu____11066) ->
                        let uu____11067 = desugar_term_aq env1 t2  in
                        (match uu____11067 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____11081;
                                   FStar_Syntax_Syntax.p = uu____11082;_}::[]
                                   -> body1
                               | uu____11083 ->
                                   let uu____11086 =
                                     let uu____11093 =
                                       let uu____11094 =
                                         let uu____11117 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____11120 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____11117, uu____11120)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11094
                                        in
                                     FStar_Syntax_Syntax.mk uu____11093  in
                                   uu____11086 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____11160 =
                               let uu____11163 =
                                 let uu____11164 =
                                   let uu____11177 =
                                     let uu____11180 =
                                       let uu____11181 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____11181]  in
                                     FStar_Syntax_Subst.close uu____11180
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____11177)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____11164  in
                               FStar_All.pipe_left mk1 uu____11163  in
                             (uu____11160, aq))
                     in
                  (match uu____10995 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____11238 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____11238, aq)
                       else (tm, aq))
               in
            let uu____11250 = FStar_List.hd lbs  in
            (match uu____11250 with
             | (attrs,(head_pat,defn)) ->
                 let uu____11294 = is_rec || (is_app_pattern head_pat)  in
                 if uu____11294
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____11307 =
                let uu____11308 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____11308  in
              mk1 uu____11307  in
            let uu____11309 = desugar_term_aq env t1  in
            (match uu____11309 with
             | (t1',aq1) ->
                 let uu____11320 = desugar_term_aq env t2  in
                 (match uu____11320 with
                  | (t2',aq2) ->
                      let uu____11331 = desugar_term_aq env t3  in
                      (match uu____11331 with
                       | (t3',aq3) ->
                           let uu____11342 =
                             let uu____11343 =
                               let uu____11344 =
                                 let uu____11367 =
                                   let uu____11384 =
                                     let uu____11399 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____11399,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____11412 =
                                     let uu____11429 =
                                       let uu____11444 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____11444,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____11429]  in
                                   uu____11384 :: uu____11412  in
                                 (t1', uu____11367)  in
                               FStar_Syntax_Syntax.Tm_match uu____11344  in
                             mk1 uu____11343  in
                           (uu____11342, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____11643 =
              match uu____11643 with
              | (pat,wopt,b) ->
                  let uu____11665 = desugar_match_pat env pat  in
                  (match uu____11665 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____11696 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____11696
                          in
                       let uu____11701 = desugar_term_aq env1 b  in
                       (match uu____11701 with
                        | (b1,aq) ->
                            let uu____11714 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____11714, aq)))
               in
            let uu____11719 = desugar_term_aq env e  in
            (match uu____11719 with
             | (e1,aq) ->
                 let uu____11730 =
                   let uu____11763 =
                     let uu____11798 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____11798 FStar_List.unzip  in
                   FStar_All.pipe_right uu____11763
                     (fun uu____12030  ->
                        match uu____12030 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____11730 with
                  | (brs,aqs) ->
                      let uu____12263 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____12263, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____12308 = is_comp_type env t  in
              if uu____12308
              then
                let uu____12317 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____12317
              else
                (let uu____12325 = desugar_term env t  in
                 FStar_Util.Inl uu____12325)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____12339 = desugar_term_aq env e  in
            (match uu____12339 with
             | (e1,aq) ->
                 let uu____12350 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____12350, aq))
        | FStar_Parser_AST.Record (uu____12383,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____12424 = FStar_List.hd fields  in
              match uu____12424 with | (f,uu____12436) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____12482  ->
                        match uu____12482 with
                        | (g,uu____12488) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____12494,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____12508 =
                         let uu____12513 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____12513)
                          in
                       FStar_Errors.raise_error uu____12508
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
                  let uu____12521 =
                    let uu____12532 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____12563  ->
                              match uu____12563 with
                              | (f,uu____12573) ->
                                  let uu____12574 =
                                    let uu____12575 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____12575
                                     in
                                  (uu____12574, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____12532)  in
                  FStar_Parser_AST.Construct uu____12521
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____12593 =
                      let uu____12594 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____12594  in
                    FStar_Parser_AST.mk_term uu____12593
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____12596 =
                      let uu____12609 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____12639  ->
                                match uu____12639 with
                                | (f,uu____12649) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____12609)  in
                    FStar_Parser_AST.Record uu____12596  in
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
            let uu____12709 = desugar_term_aq env recterm1  in
            (match uu____12709 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____12725;
                         FStar_Syntax_Syntax.vars = uu____12726;_},args)
                      ->
                      let uu____12748 =
                        let uu____12749 =
                          let uu____12750 =
                            let uu____12765 =
                              let uu____12768 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____12769 =
                                let uu____12772 =
                                  let uu____12773 =
                                    let uu____12780 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____12780)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____12773
                                   in
                                FStar_Pervasives_Native.Some uu____12772  in
                              FStar_Syntax_Syntax.fvar uu____12768
                                FStar_Syntax_Syntax.delta_constant
                                uu____12769
                               in
                            (uu____12765, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____12750  in
                        FStar_All.pipe_left mk1 uu____12749  in
                      (uu____12748, s)
                  | uu____12807 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____12811 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____12811 with
              | (constrname,is_rec) ->
                  let uu____12826 = desugar_term_aq env e  in
                  (match uu____12826 with
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
                       let uu____12844 =
                         let uu____12845 =
                           let uu____12846 =
                             let uu____12861 =
                               let uu____12864 =
                                 let uu____12865 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____12865
                                  in
                               FStar_Syntax_Syntax.fvar uu____12864
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____12866 =
                               let uu____12875 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____12875]  in
                             (uu____12861, uu____12866)  in
                           FStar_Syntax_Syntax.Tm_app uu____12846  in
                         FStar_All.pipe_left mk1 uu____12845  in
                       (uu____12844, s))))
        | FStar_Parser_AST.NamedTyp (uu____12904,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____12913 =
              let uu____12914 = FStar_Syntax_Subst.compress tm  in
              uu____12914.FStar_Syntax_Syntax.n  in
            (match uu____12913 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____12922 =
                   let uu___283_12923 =
                     let uu____12924 =
                       let uu____12925 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____12925  in
                     FStar_Syntax_Util.exp_string uu____12924  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___283_12923.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___283_12923.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____12922, noaqs)
             | uu____12926 ->
                 let uu____12927 =
                   let uu____12932 =
                     let uu____12933 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____12933
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____12932)  in
                 FStar_Errors.raise_error uu____12927
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____12939 = desugar_term_aq env e  in
            (match uu____12939 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____12951 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____12951, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____12957 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____12958 =
              let uu____12959 =
                let uu____12968 = desugar_term env e  in (bv, b, uu____12968)
                 in
              [uu____12959]  in
            (uu____12957, uu____12958)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____12999 =
              let uu____13000 =
                let uu____13001 =
                  let uu____13008 = desugar_term env e  in (uu____13008, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____13001  in
              FStar_All.pipe_left mk1 uu____13000  in
            (uu____12999, noaqs)
        | uu____13013 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____13014 = desugar_formula env top  in
            (uu____13014, noaqs)
        | uu____13015 ->
            let uu____13016 =
              let uu____13021 =
                let uu____13022 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____13022  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____13021)  in
            FStar_Errors.raise_error uu____13016 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____13028 -> false
    | uu____13037 -> true

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
           (fun uu____13074  ->
              match uu____13074 with
              | (a,imp) ->
                  let uu____13087 = desugar_term env a  in
                  arg_withimp_e imp uu____13087))

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
        let is_requires uu____13119 =
          match uu____13119 with
          | (t1,uu____13125) ->
              let uu____13126 =
                let uu____13127 = unparen t1  in
                uu____13127.FStar_Parser_AST.tm  in
              (match uu____13126 with
               | FStar_Parser_AST.Requires uu____13128 -> true
               | uu____13135 -> false)
           in
        let is_ensures uu____13145 =
          match uu____13145 with
          | (t1,uu____13151) ->
              let uu____13152 =
                let uu____13153 = unparen t1  in
                uu____13153.FStar_Parser_AST.tm  in
              (match uu____13152 with
               | FStar_Parser_AST.Ensures uu____13154 -> true
               | uu____13161 -> false)
           in
        let is_app head1 uu____13176 =
          match uu____13176 with
          | (t1,uu____13182) ->
              let uu____13183 =
                let uu____13184 = unparen t1  in
                uu____13184.FStar_Parser_AST.tm  in
              (match uu____13183 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____13186;
                      FStar_Parser_AST.level = uu____13187;_},uu____13188,uu____13189)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____13190 -> false)
           in
        let is_smt_pat uu____13200 =
          match uu____13200 with
          | (t1,uu____13206) ->
              let uu____13207 =
                let uu____13208 = unparen t1  in
                uu____13208.FStar_Parser_AST.tm  in
              (match uu____13207 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____13211);
                             FStar_Parser_AST.range = uu____13212;
                             FStar_Parser_AST.level = uu____13213;_},uu____13214)::uu____13215::[])
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
                             FStar_Parser_AST.range = uu____13254;
                             FStar_Parser_AST.level = uu____13255;_},uu____13256)::uu____13257::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____13282 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____13314 = head_and_args t1  in
          match uu____13314 with
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
                   let thunk_ens uu____13412 =
                     match uu____13412 with
                     | (e,i) ->
                         let uu____13423 = thunk_ens_ e  in (uu____13423, i)
                      in
                   let fail_lemma uu____13435 =
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
                         let uu____13515 =
                           let uu____13522 =
                             let uu____13529 = thunk_ens ens  in
                             [uu____13529; nil_pat]  in
                           req_true :: uu____13522  in
                         unit_tm :: uu____13515
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____13576 =
                           let uu____13583 =
                             let uu____13590 = thunk_ens ens  in
                             [uu____13590; nil_pat]  in
                           req :: uu____13583  in
                         unit_tm :: uu____13576
                     | ens::smtpat::[] when
                         (((let uu____13639 = is_requires ens  in
                            Prims.op_Negation uu____13639) &&
                             (let uu____13641 = is_smt_pat ens  in
                              Prims.op_Negation uu____13641))
                            &&
                            (let uu____13643 = is_decreases ens  in
                             Prims.op_Negation uu____13643))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____13644 =
                           let uu____13651 =
                             let uu____13658 = thunk_ens ens  in
                             [uu____13658; smtpat]  in
                           req_true :: uu____13651  in
                         unit_tm :: uu____13644
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____13705 =
                           let uu____13712 =
                             let uu____13719 = thunk_ens ens  in
                             [uu____13719; nil_pat; dec]  in
                           req_true :: uu____13712  in
                         unit_tm :: uu____13705
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13779 =
                           let uu____13786 =
                             let uu____13793 = thunk_ens ens  in
                             [uu____13793; smtpat; dec]  in
                           req_true :: uu____13786  in
                         unit_tm :: uu____13779
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____13853 =
                           let uu____13860 =
                             let uu____13867 = thunk_ens ens  in
                             [uu____13867; nil_pat; dec]  in
                           req :: uu____13860  in
                         unit_tm :: uu____13853
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13927 =
                           let uu____13934 =
                             let uu____13941 = thunk_ens ens  in
                             [uu____13941; smtpat]  in
                           req :: uu____13934  in
                         unit_tm :: uu____13927
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____14006 =
                           let uu____14013 =
                             let uu____14020 = thunk_ens ens  in
                             [uu____14020; dec; smtpat]  in
                           req :: uu____14013  in
                         unit_tm :: uu____14006
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____14082 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____14082, args)
               | FStar_Parser_AST.Name l when
                   (let uu____14110 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____14110
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____14111 =
                     let uu____14118 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14118, [])  in
                   (uu____14111, args)
               | FStar_Parser_AST.Name l when
                   (let uu____14136 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____14136
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____14137 =
                     let uu____14144 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14144, [])  in
                   (uu____14137, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____14160 =
                     let uu____14167 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14167, [])  in
                   (uu____14160, [(t1, FStar_Parser_AST.Nothing)])
               | uu____14190 ->
                   let default_effect =
                     let uu____14192 = FStar_Options.ml_ish ()  in
                     if uu____14192
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____14195 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____14195
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____14197 =
                     let uu____14204 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14204, [])  in
                   (uu____14197, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____14227 = pre_process_comp_typ t  in
        match uu____14227 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____14276 =
                  let uu____14281 =
                    let uu____14282 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____14282
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____14281)  in
                fail1 uu____14276)
             else ();
             (let is_universe uu____14293 =
                match uu____14293 with
                | (uu____14298,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____14300 = FStar_Util.take is_universe args  in
              match uu____14300 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____14359  ->
                         match uu____14359 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____14366 =
                    let uu____14381 = FStar_List.hd args1  in
                    let uu____14390 = FStar_List.tl args1  in
                    (uu____14381, uu____14390)  in
                  (match uu____14366 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____14445 =
                         let is_decrease uu____14483 =
                           match uu____14483 with
                           | (t1,uu____14493) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____14503;
                                       FStar_Syntax_Syntax.vars = uu____14504;_},uu____14505::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____14536 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____14445 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____14652  ->
                                      match uu____14652 with
                                      | (t1,uu____14662) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____14671,(arg,uu____14673)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____14702 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____14719 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____14730 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____14730
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____14734 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____14734
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____14741 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____14741
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____14745 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____14745
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____14749 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____14749
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____14753 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____14753
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____14769 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____14769
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
                                                  let uu____14854 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____14854
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
                                            | uu____14869 -> pat  in
                                          let uu____14870 =
                                            let uu____14879 =
                                              let uu____14888 =
                                                let uu____14895 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____14895, aq)  in
                                              [uu____14888]  in
                                            ens :: uu____14879  in
                                          req :: uu____14870
                                      | uu____14926 -> rest2
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
        | uu____14950 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___284_14971 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___284_14971.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___284_14971.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___285_15013 = b  in
             {
               FStar_Parser_AST.b = (uu___285_15013.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___285_15013.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___285_15013.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____15076 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____15076)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____15089 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____15089 with
             | (env1,a1) ->
                 let a2 =
                   let uu___286_15099 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___286_15099.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___286_15099.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____15125 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____15139 =
                     let uu____15142 =
                       let uu____15143 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____15143]  in
                     no_annot_abs uu____15142 body2  in
                   FStar_All.pipe_left setpos uu____15139  in
                 let uu____15158 =
                   let uu____15159 =
                     let uu____15174 =
                       let uu____15177 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____15177
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____15178 =
                       let uu____15187 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____15187]  in
                     (uu____15174, uu____15178)  in
                   FStar_Syntax_Syntax.Tm_app uu____15159  in
                 FStar_All.pipe_left mk1 uu____15158)
        | uu____15218 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____15298 = q (rest, pats, body)  in
              let uu____15305 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____15298 uu____15305
                FStar_Parser_AST.Formula
               in
            let uu____15306 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____15306 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____15315 -> failwith "impossible"  in
      let uu____15318 =
        let uu____15319 = unparen f  in uu____15319.FStar_Parser_AST.tm  in
      match uu____15318 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____15326,uu____15327) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____15338,uu____15339) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15370 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____15370
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15406 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____15406
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____15449 -> desugar_term env f

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
      let uu____15454 =
        FStar_List.fold_left
          (fun uu____15490  ->
             fun b  ->
               match uu____15490 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___287_15542 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___287_15542.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___287_15542.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___287_15542.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15559 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____15559 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___288_15579 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___288_15579.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___288_15579.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____15596 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____15454 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____15683 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15683)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____15688 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15688)
      | FStar_Parser_AST.TVariable x ->
          let uu____15692 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____15692)
      | FStar_Parser_AST.NoName t ->
          let uu____15696 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____15696)
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
               (fun uu___242_15735  ->
                  match uu___242_15735 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____15736 -> false))
           in
        let quals2 q =
          let uu____15749 =
            (let uu____15752 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____15752) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____15749
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____15766 = FStar_Ident.range_of_lid disc_name  in
                let uu____15767 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____15766;
                  FStar_Syntax_Syntax.sigquals = uu____15767;
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
            let uu____15806 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____15840  ->
                        match uu____15840 with
                        | (x,uu____15848) ->
                            let uu____15849 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____15849 with
                             | (field_name,uu____15857) ->
                                 let only_decl =
                                   ((let uu____15861 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____15861)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____15863 =
                                        let uu____15864 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____15864.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____15863)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____15880 =
                                       FStar_List.filter
                                         (fun uu___243_15884  ->
                                            match uu___243_15884 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____15885 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____15880
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___244_15898  ->
                                             match uu___244_15898 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____15899 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____15901 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____15901;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____15906 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____15906
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____15911 =
                                        let uu____15916 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____15916  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____15911;
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
                                      let uu____15920 =
                                        let uu____15921 =
                                          let uu____15928 =
                                            let uu____15931 =
                                              let uu____15932 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____15932
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____15931]  in
                                          ((false, [lb]), uu____15928)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____15921
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____15920;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____15806 FStar_List.flatten
  
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
            (lid,uu____15976,t,uu____15978,n1,uu____15980) when
            let uu____15985 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____15985 ->
            let uu____15986 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____15986 with
             | (formals,uu____16002) ->
                 (match formals with
                  | [] -> []
                  | uu____16025 ->
                      let filter_records uu___245_16039 =
                        match uu___245_16039 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____16042,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____16054 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____16056 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____16056 with
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
                      let uu____16066 = FStar_Util.first_N n1 formals  in
                      (match uu____16066 with
                       | (uu____16089,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____16115 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
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
                    let uu____16189 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____16189
                    then
                      let uu____16192 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____16192
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____16195 =
                      let uu____16200 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____16200  in
                    let uu____16201 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____16206 =
                          let uu____16209 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____16209  in
                        FStar_Syntax_Util.arrow typars uu____16206
                      else FStar_Syntax_Syntax.tun  in
                    let uu____16213 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____16195;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____16201;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____16213;
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
          let tycon_id uu___246_16264 =
            match uu___246_16264 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____16266,uu____16267) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____16277,uu____16278,uu____16279) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____16289,uu____16290,uu____16291) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____16321,uu____16322,uu____16323) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____16367) ->
                let uu____16368 =
                  let uu____16369 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16369  in
                FStar_Parser_AST.mk_term uu____16368 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____16371 =
                  let uu____16372 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16372  in
                FStar_Parser_AST.mk_term uu____16371 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____16374) ->
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
              | uu____16405 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____16411 =
                     let uu____16412 =
                       let uu____16419 = binder_to_term b  in
                       (out, uu____16419, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____16412  in
                   FStar_Parser_AST.mk_term uu____16411
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___247_16431 =
            match uu___247_16431 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____16487  ->
                       match uu____16487 with
                       | (x,t,uu____16498) ->
                           let uu____16503 =
                             let uu____16504 =
                               let uu____16509 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____16509, t)  in
                             FStar_Parser_AST.Annotated uu____16504  in
                           FStar_Parser_AST.mk_binder uu____16503
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____16511 =
                    let uu____16512 =
                      let uu____16513 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____16513  in
                    FStar_Parser_AST.mk_term uu____16512
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____16511 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____16517 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____16544  ->
                          match uu____16544 with
                          | (x,uu____16554,uu____16555) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____16517)
            | uu____16608 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___248_16647 =
            match uu___248_16647 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____16671 = typars_of_binders _env binders  in
                (match uu____16671 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____16713 =
                         let uu____16714 =
                           let uu____16715 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____16715  in
                         FStar_Parser_AST.mk_term uu____16714
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____16713 binders  in
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
            | uu____16726 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____16774 =
              FStar_List.fold_left
                (fun uu____16814  ->
                   fun uu____16815  ->
                     match (uu____16814, uu____16815) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____16906 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____16906 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____16774 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____17019 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____17019
                | uu____17020 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____17028 = desugar_abstract_tc quals env [] tc  in
              (match uu____17028 with
               | (uu____17041,uu____17042,se,uu____17044) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____17047,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____17064 =
                                 let uu____17065 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____17065  in
                               if uu____17064
                               then
                                 let uu____17066 =
                                   let uu____17071 =
                                     let uu____17072 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____17072
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____17071)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____17066
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
                           | uu____17079 ->
                               let uu____17080 =
                                 let uu____17087 =
                                   let uu____17088 =
                                     let uu____17101 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____17101)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____17088
                                    in
                                 FStar_Syntax_Syntax.mk uu____17087  in
                               uu____17080 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___289_17115 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___289_17115.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___289_17115.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___289_17115.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____17116 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____17119 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____17119
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____17132 = typars_of_binders env binders  in
              (match uu____17132 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17172 =
                           FStar_Util.for_some
                             (fun uu___249_17174  ->
                                match uu___249_17174 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____17175 -> false) quals
                            in
                         if uu____17172
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____17180 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____17180
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____17185 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___250_17189  ->
                               match uu___250_17189 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____17190 -> false))
                        in
                     if uu____17185
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____17199 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____17199
                     then
                       let uu____17202 =
                         let uu____17209 =
                           let uu____17210 = unparen t  in
                           uu____17210.FStar_Parser_AST.tm  in
                         match uu____17209 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____17231 =
                               match FStar_List.rev args with
                               | (last_arg,uu____17261)::args_rev ->
                                   let uu____17273 =
                                     let uu____17274 = unparen last_arg  in
                                     uu____17274.FStar_Parser_AST.tm  in
                                   (match uu____17273 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____17302 -> ([], args))
                               | uu____17311 -> ([], args)  in
                             (match uu____17231 with
                              | (cattributes,args1) ->
                                  let uu____17350 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____17350))
                         | uu____17361 -> (t, [])  in
                       match uu____17202 with
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
                                  (fun uu___251_17383  ->
                                     match uu___251_17383 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____17384 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____17391)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____17415 = tycon_record_as_variant trec  in
              (match uu____17415 with
               | (t,fs) ->
                   let uu____17432 =
                     let uu____17435 =
                       let uu____17436 =
                         let uu____17445 =
                           let uu____17448 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____17448  in
                         (uu____17445, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____17436  in
                     uu____17435 :: quals  in
                   desugar_tycon env d uu____17432 [t])
          | uu____17453::uu____17454 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____17621 = et  in
                match uu____17621 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____17846 ->
                         let trec = tc  in
                         let uu____17870 = tycon_record_as_variant trec  in
                         (match uu____17870 with
                          | (t,fs) ->
                              let uu____17929 =
                                let uu____17932 =
                                  let uu____17933 =
                                    let uu____17942 =
                                      let uu____17945 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____17945  in
                                    (uu____17942, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____17933
                                   in
                                uu____17932 :: quals1  in
                              collect_tcs uu____17929 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____18032 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____18032 with
                          | (env2,uu____18092,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____18241 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____18241 with
                          | (env2,uu____18301,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____18426 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____18473 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____18473 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___253_18984  ->
                             match uu___253_18984 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____19051,uu____19052);
                                    FStar_Syntax_Syntax.sigrng = uu____19053;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____19054;
                                    FStar_Syntax_Syntax.sigmeta = uu____19055;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____19056;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____19119 =
                                     typars_of_binders env1 binders  in
                                   match uu____19119 with
                                   | (env2,tpars1) ->
                                       let uu____19152 =
                                         push_tparams env2 tpars1  in
                                       (match uu____19152 with
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
                                 let uu____19187 =
                                   let uu____19208 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____19208)
                                    in
                                 [uu____19187]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____19276);
                                    FStar_Syntax_Syntax.sigrng = uu____19277;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____19279;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____19280;_},constrs,tconstr,quals1)
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
                                 let uu____19378 = push_tparams env1 tpars
                                    in
                                 (match uu____19378 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____19455  ->
                                             match uu____19455 with
                                             | (x,uu____19469) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____19477 =
                                        let uu____19506 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____19620  ->
                                                  match uu____19620 with
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
                                                        let uu____19676 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____19676
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
                                                                uu___252_19687
                                                                 ->
                                                                match uu___252_19687
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____19699
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____19707 =
                                                        let uu____19728 =
                                                          let uu____19729 =
                                                            let uu____19730 =
                                                              let uu____19745
                                                                =
                                                                let uu____19746
                                                                  =
                                                                  let uu____19749
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____19749
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____19746
                                                                 in
                                                              (name, univs1,
                                                                uu____19745,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____19730
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____19729;
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
                                                          uu____19728)
                                                         in
                                                      (name, uu____19707)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____19506
                                         in
                                      (match uu____19477 with
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
                             | uu____19986 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____20118  ->
                             match uu____20118 with
                             | (name_doc,uu____20146,uu____20147) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____20227  ->
                             match uu____20227 with
                             | (uu____20248,uu____20249,se) -> se))
                      in
                   let uu____20279 =
                     let uu____20286 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____20286 rng
                      in
                   (match uu____20279 with
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
                               (fun uu____20352  ->
                                  match uu____20352 with
                                  | (uu____20375,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____20426,tps,k,uu____20429,constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
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
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____20448 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____20465  ->
                                 match uu____20465 with
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
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binders  ->
      let uu____20506 =
        FStar_List.fold_left
          (fun uu____20537  ->
             fun b  ->
               match uu____20537 with
               | (env1,binders1) ->
                   let uu____20573 = desugar_binder env1 b  in
                   (match uu____20573 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____20594 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____20594 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____20637 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____20506 with
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
          let uu____20722 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___254_20727  ->
                    match uu___254_20727 with
                    | FStar_Syntax_Syntax.Reflectable uu____20728 -> true
                    | uu____20729 -> false))
             in
          if uu____20722
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____20732 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____20732
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
      let uu____20764 = FStar_Syntax_Util.head_and_args at1  in
      match uu____20764 with
      | (hd1,args) ->
          let uu____20809 =
            let uu____20822 =
              let uu____20823 = FStar_Syntax_Subst.compress hd1  in
              uu____20823.FStar_Syntax_Syntax.n  in
            (uu____20822, args)  in
          (match uu____20809 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____20844)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr
               ->
               let uu____20869 =
                 let uu____20874 =
                   FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_int
                    in
                 FStar_Syntax_Embeddings.unembed uu____20874 a1  in
               (match uu____20869 with
                | FStar_Pervasives_Native.Some [] ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Error_EmptyFailErrs,
                        "Found ill-applied fail, argument should be a non-empty list of integers")
                      at1.FStar_Syntax_Syntax.pos
                | FStar_Pervasives_Native.Some es ->
                    let uu____20904 =
                      let uu____20911 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____20911, false)  in
                    FStar_Pervasives_Native.Some uu____20904
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____20956) when
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
           | uu____21004 -> FStar_Pervasives_Native.None)
  
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
                  let uu____21171 = desugar_binders monad_env eff_binders  in
                  match uu____21171 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____21204 =
                          let uu____21205 =
                            let uu____21212 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____21212  in
                          FStar_List.length uu____21205  in
                        uu____21204 = (Prims.parse_int "1")  in
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
                            (uu____21252,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____21254,uu____21255,uu____21256),uu____21257)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____21290 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____21291 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____21303 = name_of_eff_decl decl  in
                             FStar_List.mem uu____21303 mandatory_members)
                          eff_decls
                         in
                      (match uu____21291 with
                       | (mandatory_members_decls,actions) ->
                           let uu____21320 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____21349  ->
                                     fun decl  ->
                                       match uu____21349 with
                                       | (env2,out) ->
                                           let uu____21369 =
                                             desugar_decl env2 decl  in
                                           (match uu____21369 with
                                            | (env3,ses) ->
                                                let uu____21382 =
                                                  let uu____21385 =
                                                    FStar_List.hd ses  in
                                                  uu____21385 :: out  in
                                                (env3, uu____21382)))
                                  (env1, []))
                              in
                           (match uu____21320 with
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
                                              (uu____21453,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21456,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____21457,
                                                                  (def,uu____21459)::
                                                                  (cps_type,uu____21461)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____21462;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____21463;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____21515 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21515 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21547 =
                                                     let uu____21548 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21549 =
                                                       let uu____21550 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21550
                                                        in
                                                     let uu____21555 =
                                                       let uu____21556 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21556
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21548;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21549;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____21555
                                                     }  in
                                                   (uu____21547, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____21563,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21566,defn),doc1)::[])
                                              when for_free ->
                                              let uu____21601 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21601 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21633 =
                                                     let uu____21634 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21635 =
                                                       let uu____21636 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21636
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21634;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21635;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____21633, doc1))
                                          | uu____21643 ->
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
                                    let uu____21675 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____21675
                                     in
                                  let uu____21676 =
                                    let uu____21677 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____21677
                                     in
                                  ([], uu____21676)  in
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
                                      let uu____21694 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____21694)  in
                                    let uu____21701 =
                                      let uu____21702 =
                                        let uu____21703 =
                                          let uu____21704 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21704
                                           in
                                        let uu____21713 = lookup1 "return"
                                           in
                                        let uu____21714 = lookup1 "bind"  in
                                        let uu____21715 =
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
                                            uu____21703;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____21713;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____21714;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____21715
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____21702
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____21701;
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
                                         (fun uu___255_21721  ->
                                            match uu___255_21721 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____21722 -> true
                                            | uu____21723 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____21737 =
                                       let uu____21738 =
                                         let uu____21739 =
                                           lookup1 "return_wp"  in
                                         let uu____21740 = lookup1 "bind_wp"
                                            in
                                         let uu____21741 =
                                           lookup1 "if_then_else"  in
                                         let uu____21742 = lookup1 "ite_wp"
                                            in
                                         let uu____21743 = lookup1 "stronger"
                                            in
                                         let uu____21744 = lookup1 "close_wp"
                                            in
                                         let uu____21745 = lookup1 "assert_p"
                                            in
                                         let uu____21746 = lookup1 "assume_p"
                                            in
                                         let uu____21747 = lookup1 "null_wp"
                                            in
                                         let uu____21748 = lookup1 "trivial"
                                            in
                                         let uu____21749 =
                                           if rr
                                           then
                                             let uu____21750 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____21750
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____21766 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____21768 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____21770 =
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
                                             uu____21739;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____21740;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____21741;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____21742;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____21743;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____21744;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____21745;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____21746;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____21747;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____21748;
                                           FStar_Syntax_Syntax.repr =
                                             uu____21749;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____21766;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____21768;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____21770
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____21738
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____21737;
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
                                          fun uu____21796  ->
                                            match uu____21796 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____21810 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____21810
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
                let uu____21834 = desugar_binders env1 eff_binders  in
                match uu____21834 with
                | (env2,binders) ->
                    let uu____21865 =
                      let uu____21876 = head_and_args defn  in
                      match uu____21876 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____21913 ->
                                let uu____21914 =
                                  let uu____21919 =
                                    let uu____21920 =
                                      let uu____21921 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____21921 " not found"
                                       in
                                    Prims.strcat "Effect " uu____21920  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____21919)
                                   in
                                FStar_Errors.raise_error uu____21914
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____21923 =
                            match FStar_List.rev args with
                            | (last_arg,uu____21953)::args_rev ->
                                let uu____21965 =
                                  let uu____21966 = unparen last_arg  in
                                  uu____21966.FStar_Parser_AST.tm  in
                                (match uu____21965 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____21994 -> ([], args))
                            | uu____22003 -> ([], args)  in
                          (match uu____21923 with
                           | (cattributes,args1) ->
                               let uu____22046 = desugar_args env2 args1  in
                               let uu____22047 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____22046, uu____22047))
                       in
                    (match uu____21865 with
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
                          (let uu____22079 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____22079 with
                           | (ed_binders,uu____22093,ed_binders_opening) ->
                               let sub1 uu____22106 =
                                 match uu____22106 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____22120 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____22120 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____22124 =
                                       let uu____22125 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____22125)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____22124
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____22134 =
                                   let uu____22135 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____22135
                                    in
                                 let uu____22150 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____22151 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____22152 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____22153 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____22154 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____22155 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____22156 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____22157 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____22158 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____22159 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____22160 =
                                   let uu____22161 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____22161
                                    in
                                 let uu____22176 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____22177 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____22178 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____22186 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____22187 =
                                          let uu____22188 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22188
                                           in
                                        let uu____22203 =
                                          let uu____22204 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22204
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____22186;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____22187;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____22203
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
                                     uu____22134;
                                   FStar_Syntax_Syntax.ret_wp = uu____22150;
                                   FStar_Syntax_Syntax.bind_wp = uu____22151;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____22152;
                                   FStar_Syntax_Syntax.ite_wp = uu____22153;
                                   FStar_Syntax_Syntax.stronger = uu____22154;
                                   FStar_Syntax_Syntax.close_wp = uu____22155;
                                   FStar_Syntax_Syntax.assert_p = uu____22156;
                                   FStar_Syntax_Syntax.assume_p = uu____22157;
                                   FStar_Syntax_Syntax.null_wp = uu____22158;
                                   FStar_Syntax_Syntax.trivial = uu____22159;
                                   FStar_Syntax_Syntax.repr = uu____22160;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____22176;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____22177;
                                   FStar_Syntax_Syntax.actions = uu____22178;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____22221 =
                                     let uu____22222 =
                                       let uu____22229 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____22229
                                        in
                                     FStar_List.length uu____22222  in
                                   uu____22221 = (Prims.parse_int "1")  in
                                 let uu____22254 =
                                   let uu____22257 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____22257 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____22254;
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
                                             let uu____22279 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____22279
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____22281 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____22281
                                 then
                                   let reflect_lid =
                                     let uu____22285 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____22285
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
    let uu____22295 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____22295 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____22346 ->
              let uu____22347 =
                let uu____22348 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____22348
                 in
              Prims.strcat "\n  " uu____22347
          | uu____22349 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____22362  ->
               match uu____22362 with
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
          let uu____22380 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____22380
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____22382 =
          let uu____22391 = FStar_Syntax_Syntax.as_arg arg  in [uu____22391]
           in
        FStar_Syntax_Util.mk_app fv uu____22382

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22416 = desugar_decl_noattrs env d  in
      match uu____22416 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____22434 = mk_comment_attr d  in uu____22434 :: attrs1  in
          let uu____22435 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___290_22441 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___290_22441.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___290_22441.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___290_22441.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___290_22441.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___291_22443 = sigelt  in
                      let uu____22444 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____22450 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____22450) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___291_22443.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___291_22443.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___291_22443.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___291_22443.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____22444
                      })) sigelts
             in
          (env1, uu____22435)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22471 = desugar_decl_aux env d  in
      match uu____22471 with
      | (env1,ses) ->
          let uu____22482 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____22482)

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
      | FStar_Parser_AST.Fsdoc uu____22510 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____22518 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____22518, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____22555  ->
                 match uu____22555 with | (x,uu____22563) -> x) tcs
             in
          let uu____22568 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____22568 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____22590;
                    FStar_Parser_AST.prange = uu____22591;_},uu____22592)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____22601;
                    FStar_Parser_AST.prange = uu____22602;_},uu____22603)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____22618;
                         FStar_Parser_AST.prange = uu____22619;_},uu____22620);
                    FStar_Parser_AST.prange = uu____22621;_},uu____22622)::[]
                   -> false
               | (p,uu____22650)::[] ->
                   let uu____22659 = is_app_pattern p  in
                   Prims.op_Negation uu____22659
               | uu____22660 -> false)
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
            let uu____22733 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____22733 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____22745 =
                     let uu____22746 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____22746.FStar_Syntax_Syntax.n  in
                   match uu____22745 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____22756) ->
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
                         | uu____22789::uu____22790 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____22793 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___256_22808  ->
                                     match uu___256_22808 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____22811;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____22812;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____22813;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____22814;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____22815;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____22816;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____22817;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____22829;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____22830;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____22831;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____22832;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____22833;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____22834;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____22848 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____22879  ->
                                   match uu____22879 with
                                   | (uu____22892,(uu____22893,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____22848
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____22911 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____22911
                         then
                           let uu____22914 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___292_22928 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___293_22930 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___293_22930.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___293_22930.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___292_22928.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___292_22928.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___292_22928.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___292_22928.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___292_22928.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___292_22928.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____22914)
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
                   | uu____22957 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____22963 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____22982 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____22963 with
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
                       let uu___294_23018 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___294_23018.FStar_Parser_AST.prange)
                       }
                   | uu____23025 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___295_23032 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___295_23032.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___295_23032.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___295_23032.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____23068 id1 =
                   match uu____23068 with
                   | (env1,ses) ->
                       let main =
                         let uu____23089 =
                           let uu____23090 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____23090  in
                         FStar_Parser_AST.mk_term uu____23089
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
                       let uu____23140 = desugar_decl env1 id_decl  in
                       (match uu____23140 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____23158 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____23158 FStar_Util.set_elements
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
            let uu____23181 = close_fun env t  in
            desugar_term env uu____23181  in
          let quals1 =
            let uu____23185 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____23185
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____23191 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____23191;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____23199 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____23199 with
           | (t,uu____23213) ->
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
            let uu____23243 =
              let uu____23250 = FStar_Syntax_Syntax.null_binder t  in
              [uu____23250]  in
            let uu____23263 =
              let uu____23266 =
                let uu____23267 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____23267  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____23266
               in
            FStar_Syntax_Util.arrow uu____23243 uu____23263  in
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
            let uu____23328 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____23328 with
            | FStar_Pervasives_Native.None  ->
                let uu____23331 =
                  let uu____23336 =
                    let uu____23337 =
                      let uu____23338 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____23338 " not found"  in
                    Prims.strcat "Effect name " uu____23337  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____23336)  in
                FStar_Errors.raise_error uu____23331
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____23342 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____23360 =
                  let uu____23363 =
                    let uu____23364 = desugar_term env t  in
                    ([], uu____23364)  in
                  FStar_Pervasives_Native.Some uu____23363  in
                (uu____23360, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____23377 =
                  let uu____23380 =
                    let uu____23381 = desugar_term env wp  in
                    ([], uu____23381)  in
                  FStar_Pervasives_Native.Some uu____23380  in
                let uu____23388 =
                  let uu____23391 =
                    let uu____23392 = desugar_term env t  in
                    ([], uu____23392)  in
                  FStar_Pervasives_Native.Some uu____23391  in
                (uu____23377, uu____23388)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____23404 =
                  let uu____23407 =
                    let uu____23408 = desugar_term env t  in
                    ([], uu____23408)  in
                  FStar_Pervasives_Native.Some uu____23407  in
                (FStar_Pervasives_Native.None, uu____23404)
             in
          (match uu____23342 with
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
            let uu____23442 =
              let uu____23443 =
                let uu____23450 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____23450, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____23443  in
            {
              FStar_Syntax_Syntax.sigel = uu____23442;
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
      let uu____23476 =
        FStar_List.fold_left
          (fun uu____23496  ->
             fun d  ->
               match uu____23496 with
               | (env1,sigelts) ->
                   let uu____23516 = desugar_decl env1 d  in
                   (match uu____23516 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____23476 with
      | (env1,sigelts) ->
          let rec forward acc uu___258_23561 =
            match uu___258_23561 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____23575,FStar_Syntax_Syntax.Sig_let uu____23576) ->
                     let uu____23589 =
                       let uu____23592 =
                         let uu___296_23593 = se2  in
                         let uu____23594 =
                           let uu____23597 =
                             FStar_List.filter
                               (fun uu___257_23611  ->
                                  match uu___257_23611 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____23615;
                                           FStar_Syntax_Syntax.vars =
                                             uu____23616;_},uu____23617);
                                      FStar_Syntax_Syntax.pos = uu____23618;
                                      FStar_Syntax_Syntax.vars = uu____23619;_}
                                      when
                                      let uu____23642 =
                                        let uu____23643 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____23643
                                         in
                                      uu____23642 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____23644 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____23597
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___296_23593.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___296_23593.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___296_23593.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___296_23593.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____23594
                         }  in
                       uu____23592 :: se1 :: acc  in
                     forward uu____23589 sigelts1
                 | uu____23649 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____23657 = forward [] sigelts  in (env1, uu____23657)
  
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
          | (FStar_Pervasives_Native.None ,uu____23718) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____23722;
               FStar_Syntax_Syntax.exports = uu____23723;
               FStar_Syntax_Syntax.is_interface = uu____23724;_},FStar_Parser_AST.Module
             (current_lid,uu____23726)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____23734) ->
              let uu____23737 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____23737
           in
        let uu____23742 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____23778 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23778, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____23795 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23795, mname, decls, false)
           in
        match uu____23742 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____23825 = desugar_decls env2 decls  in
            (match uu____23825 with
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
          let uu____23887 =
            (FStar_Options.interactive ()) &&
              (let uu____23889 =
                 let uu____23890 =
                   let uu____23891 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____23891  in
                 FStar_Util.get_file_extension uu____23890  in
               FStar_List.mem uu____23889 ["fsti"; "fsi"])
             in
          if uu____23887 then as_interface m else m  in
        let uu____23895 = desugar_modul_common curmod env m1  in
        match uu____23895 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____23913 = FStar_Syntax_DsEnv.pop ()  in
              (uu____23913, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____23933 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____23933 with
      | (env1,modul,pop_when_done) ->
          let uu____23947 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____23947 with
           | (env2,modul1) ->
               ((let uu____23959 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____23959
                 then
                   let uu____23960 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____23960
                 else ());
                (let uu____23962 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____23962, modul1))))
  
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
        (fun uu____24009  ->
           let uu____24010 = desugar_modul env modul  in
           match uu____24010 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____24051  ->
           let uu____24052 = desugar_decls env decls  in
           match uu____24052 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____24106  ->
             let uu____24107 = desugar_partial_modul modul env a_modul  in
             match uu____24107 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____24193 ->
                  let t =
                    let uu____24201 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____24201  in
                  let uu____24212 =
                    let uu____24213 = FStar_Syntax_Subst.compress t  in
                    uu____24213.FStar_Syntax_Syntax.n  in
                  (match uu____24212 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____24223,uu____24224)
                       -> bs1
                   | uu____24245 -> failwith "Impossible")
               in
            let uu____24252 =
              let uu____24259 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____24259
                FStar_Syntax_Syntax.t_unit
               in
            match uu____24252 with
            | (binders,uu____24261,binders_opening) ->
                let erase_term t =
                  let uu____24269 =
                    let uu____24270 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____24270  in
                  FStar_Syntax_Subst.close binders uu____24269  in
                let erase_tscheme uu____24288 =
                  match uu____24288 with
                  | (us,t) ->
                      let t1 =
                        let uu____24308 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____24308 t  in
                      let uu____24311 =
                        let uu____24312 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____24312  in
                      ([], uu____24311)
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
                    | uu____24331 ->
                        let bs =
                          let uu____24339 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____24339  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____24371 =
                          let uu____24372 =
                            let uu____24375 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____24375  in
                          uu____24372.FStar_Syntax_Syntax.n  in
                        (match uu____24371 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____24377,uu____24378) -> bs1
                         | uu____24399 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____24406 =
                      let uu____24407 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____24407  in
                    FStar_Syntax_Subst.close binders uu____24406  in
                  let uu___297_24408 = action  in
                  let uu____24409 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____24410 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___297_24408.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___297_24408.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____24409;
                    FStar_Syntax_Syntax.action_typ = uu____24410
                  }  in
                let uu___298_24411 = ed  in
                let uu____24412 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____24413 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____24414 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____24415 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____24416 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____24417 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____24418 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____24419 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____24420 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____24421 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____24422 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____24423 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____24424 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____24425 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____24426 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____24427 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___298_24411.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___298_24411.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____24412;
                  FStar_Syntax_Syntax.signature = uu____24413;
                  FStar_Syntax_Syntax.ret_wp = uu____24414;
                  FStar_Syntax_Syntax.bind_wp = uu____24415;
                  FStar_Syntax_Syntax.if_then_else = uu____24416;
                  FStar_Syntax_Syntax.ite_wp = uu____24417;
                  FStar_Syntax_Syntax.stronger = uu____24418;
                  FStar_Syntax_Syntax.close_wp = uu____24419;
                  FStar_Syntax_Syntax.assert_p = uu____24420;
                  FStar_Syntax_Syntax.assume_p = uu____24421;
                  FStar_Syntax_Syntax.null_wp = uu____24422;
                  FStar_Syntax_Syntax.trivial = uu____24423;
                  FStar_Syntax_Syntax.repr = uu____24424;
                  FStar_Syntax_Syntax.return_repr = uu____24425;
                  FStar_Syntax_Syntax.bind_repr = uu____24426;
                  FStar_Syntax_Syntax.actions = uu____24427;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___298_24411.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___299_24443 = se  in
                  let uu____24444 =
                    let uu____24445 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____24445  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24444;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___299_24443.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___299_24443.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___299_24443.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___299_24443.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___300_24449 = se  in
                  let uu____24450 =
                    let uu____24451 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24451
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24450;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___300_24449.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___300_24449.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___300_24449.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___300_24449.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____24453 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____24454 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____24454 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____24466 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____24466
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____24468 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____24468)
  