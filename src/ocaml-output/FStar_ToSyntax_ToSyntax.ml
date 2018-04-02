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
  fun uu___84_58  ->
    match uu___84_58 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____63 -> FStar_Pervasives_Native.None
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___85_76  ->
        match uu___85_76 with
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
  fun uu___86_83  ->
    match uu___86_83 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___87_92  ->
    match uu___87_92 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____95 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____99 .
    FStar_Parser_AST.imp ->
      'Auu____99 ->
        ('Auu____99,FStar_Syntax_Syntax.arg_qualifier
                      FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____119 .
    FStar_Parser_AST.imp ->
      'Auu____119 ->
        ('Auu____119,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____136 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____151 -> true
            | uu____156 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____161 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____165 =
      let uu____166 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____166  in
    FStar_Parser_AST.mk_term uu____165 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____170 =
      let uu____171 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____171  in
    FStar_Parser_AST.mk_term uu____170 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____178 =
        let uu____179 = unparen t  in uu____179.FStar_Parser_AST.tm  in
      match uu____178 with
      | FStar_Parser_AST.Name l ->
          let uu____181 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____181 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____187) ->
          let uu____200 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____200 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____206,uu____207) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____210,uu____211) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____216,t1) -> is_comp_type env t1
      | uu____218 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____228 =
          let uu____231 =
            let uu____232 =
              let uu____237 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____237, r)  in
            FStar_Ident.mk_ident uu____232  in
          [uu____231]  in
        FStar_All.pipe_right uu____228 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____245 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____245 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____273 =
              let uu____274 =
                let uu____275 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____275 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____274 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____273  in
          let fallback uu____281 =
            let uu____282 = FStar_Ident.text_of_id op  in
            match uu____282 with
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
                let uu____285 = FStar_Options.ml_ish ()  in
                if uu____285
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
            | uu____289 -> FStar_Pervasives_Native.None  in
          let uu____290 =
            let uu____297 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____297  in
          match uu____290 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____309 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____325 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____325
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____364 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____368 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____368 with | (env1,uu____380) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____383,term) ->
          let uu____385 = free_type_vars env term  in (env, uu____385)
      | FStar_Parser_AST.TAnnotated (id1,uu____391) ->
          let uu____392 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____392 with | (env1,uu____404) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____408 = free_type_vars env t  in (env, uu____408)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____415 =
        let uu____416 = unparen t  in uu____416.FStar_Parser_AST.tm  in
      match uu____415 with
      | FStar_Parser_AST.Labeled uu____419 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____429 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____429 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____442 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____449 -> []
      | FStar_Parser_AST.Uvar uu____450 -> []
      | FStar_Parser_AST.Var uu____451 -> []
      | FStar_Parser_AST.Projector uu____452 -> []
      | FStar_Parser_AST.Discrim uu____457 -> []
      | FStar_Parser_AST.Name uu____458 -> []
      | FStar_Parser_AST.Requires (t1,uu____460) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____466) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____471,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____489,ts) ->
          FStar_List.collect
            (fun uu____510  ->
               match uu____510 with | (t1,uu____518) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____519,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____527) ->
          let uu____528 = free_type_vars env t1  in
          let uu____531 = free_type_vars env t2  in
          FStar_List.append uu____528 uu____531
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____536 = free_type_vars_b env b  in
          (match uu____536 with
           | (env1,f) ->
               let uu____551 = free_type_vars env1 t1  in
               FStar_List.append f uu____551)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____560 =
            FStar_List.fold_left
              (fun uu____580  ->
                 fun binder  ->
                   match uu____580 with
                   | (env1,free) ->
                       let uu____600 = free_type_vars_b env1 binder  in
                       (match uu____600 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____560 with
           | (env1,free) ->
               let uu____631 = free_type_vars env1 body  in
               FStar_List.append free uu____631)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____640 =
            FStar_List.fold_left
              (fun uu____660  ->
                 fun binder  ->
                   match uu____660 with
                   | (env1,free) ->
                       let uu____680 = free_type_vars_b env1 binder  in
                       (match uu____680 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____640 with
           | (env1,free) ->
               let uu____711 = free_type_vars env1 body  in
               FStar_List.append free uu____711)
      | FStar_Parser_AST.Project (t1,uu____715) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____719 -> []
      | FStar_Parser_AST.Let uu____726 -> []
      | FStar_Parser_AST.LetOpen uu____747 -> []
      | FStar_Parser_AST.If uu____752 -> []
      | FStar_Parser_AST.QForall uu____759 -> []
      | FStar_Parser_AST.QExists uu____772 -> []
      | FStar_Parser_AST.Record uu____785 -> []
      | FStar_Parser_AST.Match uu____798 -> []
      | FStar_Parser_AST.TryWith uu____813 -> []
      | FStar_Parser_AST.Bind uu____828 -> []
      | FStar_Parser_AST.Quote uu____835 -> []
      | FStar_Parser_AST.VQuote uu____840 -> []
      | FStar_Parser_AST.Antiquote uu____841 -> []
      | FStar_Parser_AST.Seq uu____846 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____893 =
        let uu____894 = unparen t1  in uu____894.FStar_Parser_AST.tm  in
      match uu____893 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____936 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____956 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____956  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____974 =
                     let uu____975 =
                       let uu____980 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____980)  in
                     FStar_Parser_AST.TAnnotated uu____975  in
                   FStar_Parser_AST.mk_binder uu____974 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
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
        let uu____993 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____993  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1011 =
                     let uu____1012 =
                       let uu____1017 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1017)  in
                     FStar_Parser_AST.TAnnotated uu____1012  in
                   FStar_Parser_AST.mk_binder uu____1011
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1019 =
             let uu____1020 = unparen t  in uu____1020.FStar_Parser_AST.tm
              in
           match uu____1019 with
           | FStar_Parser_AST.Product uu____1021 -> t
           | uu____1028 ->
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
      | uu____1060 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1066,uu____1067) -> true
    | FStar_Parser_AST.PatVar (uu____1072,uu____1073) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1079) -> is_var_pattern p1
    | uu____1092 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1097) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1110;
           FStar_Parser_AST.prange = uu____1111;_},uu____1112)
        -> true
    | uu____1123 -> false
  
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
    | uu____1135 -> p
  
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
            let uu____1199 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1199 with
             | (name,args,uu____1242) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1292);
               FStar_Parser_AST.prange = uu____1293;_},args)
            when is_top_level1 ->
            let uu____1303 =
              let uu____1308 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1308  in
            (uu____1303, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1330);
               FStar_Parser_AST.prange = uu____1331;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1361 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1405 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1406,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1409 -> acc
      | FStar_Parser_AST.PatTvar uu____1410 -> acc
      | FStar_Parser_AST.PatOp uu____1417 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1425) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1434) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1449 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1449
      | FStar_Parser_AST.PatAscribed (pat,uu____1457) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1513 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1547 -> false
  
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
  fun uu___88_1591  ->
    match uu___88_1591 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1598 -> failwith "Impossible"
  
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
      fun uu___89_1623  ->
        match uu___89_1623 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1639 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1639, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1644 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1644 with
             | (env1,a1) ->
                 (((let uu___113_1664 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___113_1664.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___113_1664.FStar_Syntax_Syntax.index);
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
  fun uu____1691  ->
    match uu____1691 with
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
      let uu____1759 =
        let uu____1774 =
          let uu____1775 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1775  in
        let uu____1776 =
          let uu____1785 =
            let uu____1792 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1792)  in
          [uu____1785]  in
        (uu____1774, uu____1776)  in
      FStar_Syntax_Syntax.Tm_app uu____1759  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1825 =
        let uu____1840 =
          let uu____1841 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1841  in
        let uu____1842 =
          let uu____1851 =
            let uu____1858 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1858)  in
          [uu____1851]  in
        (uu____1840, uu____1842)  in
      FStar_Syntax_Syntax.Tm_app uu____1825  in
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
          let uu____1901 =
            let uu____1916 =
              let uu____1917 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____1917  in
            let uu____1918 =
              let uu____1927 =
                let uu____1934 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____1934)  in
              let uu____1937 =
                let uu____1946 =
                  let uu____1953 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____1953)  in
                [uu____1946]  in
              uu____1927 :: uu____1937  in
            (uu____1916, uu____1918)  in
          FStar_Syntax_Syntax.Tm_app uu____1901  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___90_1984  ->
    match uu___90_1984 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1985 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1993 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1993)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2008 =
      let uu____2009 = unparen t  in uu____2009.FStar_Parser_AST.tm  in
    match uu____2008 with
    | FStar_Parser_AST.Wild  ->
        let uu____2014 =
          let uu____2015 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2015  in
        FStar_Util.Inr uu____2014
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2026)) ->
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
        ((let uu____2048 = Obj.magic ()  in ());
         (let u1 = desugar_maybe_non_constant_universe t1  in
          let u2 = desugar_maybe_non_constant_universe t2  in
          match (u1, u2) with
          | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
          | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
              let uu____2091 = sum_to_universe u n1  in
              FStar_Util.Inr uu____2091
          | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
              let uu____2102 = sum_to_universe u n1  in
              FStar_Util.Inr uu____2102
          | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
              let uu____2113 =
                let uu____2118 =
                  let uu____2119 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat
                    "This universe might contain a sum of two universe variables "
                    uu____2119
                   in
                (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                  uu____2118)
                 in
              FStar_Errors.raise_error uu____2113 t.FStar_Parser_AST.range))
    | FStar_Parser_AST.App uu____2124 ->
        let rec aux t1 univargs =
          let uu____2154 =
            let uu____2155 = unparen t1  in uu____2155.FStar_Parser_AST.tm
             in
          match uu____2154 with
          | FStar_Parser_AST.App (t2,targ,uu____2162) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              ((let uu____2174 = Obj.magic ()  in ());
               if
                 FStar_List.existsb
                   (fun uu___91_2185  ->
                      match uu___91_2185 with
                      | FStar_Util.Inr uu____2190 -> true
                      | uu____2191 -> false) univargs
               then
                 (let uu____2196 =
                    let uu____2197 =
                      FStar_List.map
                        (fun uu___92_2206  ->
                           match uu___92_2206 with
                           | FStar_Util.Inl n1 -> int_to_universe n1
                           | FStar_Util.Inr u -> u) univargs
                       in
                    FStar_Syntax_Syntax.U_max uu____2197  in
                  FStar_Util.Inr uu____2196)
               else
                 (let nargs =
                    FStar_List.map
                      (fun uu___93_2223  ->
                         match uu___93_2223 with
                         | FStar_Util.Inl n1 -> n1
                         | FStar_Util.Inr uu____2229 -> failwith "impossible")
                      univargs
                     in
                  let uu____2230 =
                    FStar_List.fold_left
                      (fun m  -> fun n1  -> if m > n1 then m else n1)
                      (Prims.parse_int "0") nargs
                     in
                  FStar_Util.Inl uu____2230))
          | uu____2236 ->
              let uu____2237 =
                let uu____2242 =
                  let uu____2243 =
                    let uu____2244 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2244 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2243  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2242)  in
              FStar_Errors.raise_error uu____2237 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2253 ->
        let uu____2254 =
          let uu____2259 =
            let uu____2260 =
              let uu____2261 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2261 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2260  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2259)  in
        FStar_Errors.raise_error uu____2254 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let (check_no_aq : FStar_Syntax_Syntax.antiquotations -> Prims.unit) =
  fun aq  ->
    match aq with
    | [] -> ()
    | (bv,b,e)::uu____2290 ->
        let uu____2313 =
          let uu____2318 =
            let uu____2319 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____2319
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____2318)  in
        FStar_Errors.raise_error uu____2313 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____2325 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2325) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2350 = FStar_List.hd fields  in
        match uu____2350 with
        | (f,uu____2360) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2370 =
                match uu____2370 with
                | (f',uu____2376) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2378 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____2378
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
              (let uu____2382 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2382);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2631 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2638 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2639 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2641,pats1) ->
                let aux out uu____2675 =
                  match uu____2675 with
                  | (p2,uu____2687) ->
                      let intersection =
                        let uu____2695 = pat_vars p2  in
                        FStar_Util.set_intersect uu____2695 out  in
                      let uu____2698 = FStar_Util.set_is_empty intersection
                         in
                      if uu____2698
                      then
                        let uu____2701 = pat_vars p2  in
                        FStar_Util.set_union out uu____2701
                      else
                        (let duplicate_bv =
                           let uu____2706 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____2706  in
                         let uu____2709 =
                           let uu____2714 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____2714)
                            in
                         FStar_Errors.raise_error uu____2709 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____2734 = pat_vars p1  in
              FStar_All.pipe_right uu____2734 FStar_Pervasives.ignore
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____2754 =
                  let uu____2755 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____2755  in
                if uu____2754
                then ()
                else
                  (let nonlinear_vars =
                     let uu____2762 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____2762  in
                   let first_nonlinear_var =
                     let uu____2766 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____2766  in
                   let uu____2769 =
                     let uu____2774 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____2774)  in
                   FStar_Errors.raise_error uu____2769 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2778) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2779) -> ()
         | (true ,uu____2786) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_Syntax_DsEnv.push_bv_mutable
           else FStar_Syntax_DsEnv.push_bv  in
         let resolvex l e x =
           let uu____2821 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2821 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2835 ->
               let uu____2838 = push_bv_maybe_mut e x  in
               (match uu____2838 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2925 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2941 =
                 let uu____2942 =
                   let uu____2943 =
                     let uu____2950 =
                       let uu____2951 =
                         let uu____2956 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2956, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2951  in
                     (uu____2950, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2943  in
                 {
                   FStar_Parser_AST.pat = uu____2942;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2941
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____2973 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____2974 = aux loc env1 p2  in
                 match uu____2974 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___114_3028 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___115_3033 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___115_3033.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___115_3033.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___114_3028.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___116_3035 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___117_3040 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___117_3040.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___117_3040.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___116_3035.FStar_Syntax_Syntax.p)
                           }
                       | uu____3041 when top -> p4
                       | uu____3042 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____3045 =
                       match binder with
                       | LetBinder uu____3058 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____3078 = close_fun env1 t  in
                             desugar_term env1 uu____3078  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____3080 -> true)
                            then
                              (let uu____3081 =
                                 let uu____3086 =
                                   let uu____3087 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____3088 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____3089 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3087 uu____3088 uu____3089
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3086)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3081)
                            else ();
                            (let uu____3091 = annot_pat_var p3 t1  in
                             (uu____3091,
                               (LocalBinder
                                  ((let uu___118_3097 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___118_3097.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___118_3097.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____3045 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3119 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3119, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3130 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3130, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3151 = resolvex loc env1 x  in
               (match uu____3151 with
                | (loc1,env2,xbv) ->
                    let uu____3173 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3173, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3194 = resolvex loc env1 x  in
               (match uu____3194 with
                | (loc1,env2,xbv) ->
                    let uu____3216 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3216, imp))
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
               let uu____3228 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3228, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3252;_},args)
               ->
               let uu____3258 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3299  ->
                        match uu____3299 with
                        | (loc1,env2,args1) ->
                            let uu____3347 = aux loc1 env2 arg  in
                            (match uu____3347 with
                             | (loc2,env3,uu____3376,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____3258 with
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
                    let uu____3446 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3446, false))
           | FStar_Parser_AST.PatApp uu____3463 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3485 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3518  ->
                        match uu____3518 with
                        | (loc1,env2,pats1) ->
                            let uu____3550 = aux loc1 env2 pat  in
                            (match uu____3550 with
                             | (loc2,env3,uu____3575,pat1,uu____3577) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3485 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3620 =
                        let uu____3623 =
                          let uu____3628 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3628  in
                        let uu____3629 =
                          let uu____3630 =
                            let uu____3643 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3643, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3630  in
                        FStar_All.pipe_left uu____3623 uu____3629  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3675 =
                               let uu____3676 =
                                 let uu____3689 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3689, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3676  in
                             FStar_All.pipe_left (pos_r r) uu____3675) pats1
                        uu____3620
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
               let uu____3733 =
                 FStar_List.fold_left
                   (fun uu____3773  ->
                      fun p2  ->
                        match uu____3773 with
                        | (loc1,env2,pats) ->
                            let uu____3822 = aux loc1 env2 p2  in
                            (match uu____3822 with
                             | (loc2,env3,uu____3851,pat,uu____3853) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3733 with
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
                    let uu____3948 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____3948 with
                     | (constr,uu____3970) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3973 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3975 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3975, false)))
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
                      (fun uu____4046  ->
                         match uu____4046 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4076  ->
                         match uu____4076 with
                         | (f,uu____4082) ->
                             let uu____4083 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4109  ->
                                       match uu____4109 with
                                       | (g,uu____4115) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____4083 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4120,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____4127 =
                   let uu____4128 =
                     let uu____4135 =
                       let uu____4136 =
                         let uu____4137 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____4137  in
                       FStar_Parser_AST.mk_pattern uu____4136
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____4135, args)  in
                   FStar_Parser_AST.PatApp uu____4128  in
                 FStar_Parser_AST.mk_pattern uu____4127
                   p1.FStar_Parser_AST.prange
                  in
               let uu____4140 = aux loc env1 app  in
               (match uu____4140 with
                | (env2,e,b,p2,uu____4169) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4197 =
                            let uu____4198 =
                              let uu____4211 =
                                let uu___119_4212 = fv  in
                                let uu____4213 =
                                  let uu____4216 =
                                    let uu____4217 =
                                      let uu____4224 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4224)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4217
                                     in
                                  FStar_Pervasives_Native.Some uu____4216  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___119_4212.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___119_4212.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4213
                                }  in
                              (uu____4211, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____4198  in
                          FStar_All.pipe_left pos uu____4197
                      | uu____4251 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4301 = aux' true loc env1 p2  in
               (match uu____4301 with
                | (loc1,env2,var,p3,uu____4328) ->
                    let uu____4333 =
                      FStar_List.fold_left
                        (fun uu____4365  ->
                           fun p4  ->
                             match uu____4365 with
                             | (loc2,env3,ps1) ->
                                 let uu____4398 = aux' true loc2 env3 p4  in
                                 (match uu____4398 with
                                  | (loc3,env4,uu____4423,p5,uu____4425) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____4333 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4476 ->
               let uu____4477 = aux' true loc env1 p1  in
               (match uu____4477 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4517 = aux_maybe_or env p  in
         match uu____4517 with
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
            let uu____4576 =
              let uu____4577 =
                let uu____4588 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4588,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4577  in
            (env, uu____4576, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4616 =
                  let uu____4617 =
                    let uu____4622 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4622, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4617  in
                mklet uu____4616
            | FStar_Parser_AST.PatVar (x,uu____4624) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4630);
                   FStar_Parser_AST.prange = uu____4631;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4651 =
                  let uu____4652 =
                    let uu____4663 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____4664 =
                      let uu____4671 = desugar_term env t  in
                      (uu____4671, tacopt1)  in
                    (uu____4663, uu____4664)  in
                  LetBinder uu____4652  in
                (env, uu____4651, [])
            | uu____4682 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4692 = desugar_data_pat env p is_mut  in
             match uu____4692 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4721;
                       FStar_Syntax_Syntax.p = uu____4722;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4727;
                       FStar_Syntax_Syntax.p = uu____4728;_}::[] -> []
                   | uu____4733 -> p1  in
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
  fun uu____4740  ->
    fun env  ->
      fun pat  ->
        let uu____4743 = desugar_data_pat env pat false  in
        match uu____4743 with | (env1,uu____4759,pat1) -> (env1, pat1)

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
      let uu____4778 = desugar_term_aq env e  in
      match uu____4778 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____4795 = desugar_typ_aq env e  in
      match uu____4795 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____4805  ->
        fun range  ->
          match uu____4805 with
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
              ((let uu____4815 =
                  let uu____4816 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4816  in
                if uu____4815
                then
                  let uu____4817 =
                    let uu____4822 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4822)  in
                  FStar_Errors.log_issue range uu____4817
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
                  let uu____4827 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____4827 range  in
                let lid1 =
                  let uu____4831 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____4831 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4841) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____4850 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____4850 range  in
                           let private_fv =
                             let uu____4852 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4852 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___120_4853 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___120_4853.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___120_4853.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4854 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4861 =
                        let uu____4866 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4866)
                         in
                      FStar_Errors.raise_error uu____4861 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4882 =
                  let uu____4885 =
                    let uu____4886 =
                      let uu____4901 =
                        let uu____4910 =
                          let uu____4917 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4917)  in
                        [uu____4910]  in
                      (lid1, uu____4901)  in
                    FStar_Syntax_Syntax.Tm_app uu____4886  in
                  FStar_Syntax_Syntax.mk uu____4885  in
                uu____4882 FStar_Pervasives_Native.None range))

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
            let uu____4956 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4956 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____5003;
                              FStar_Syntax_Syntax.vars = uu____5004;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5027 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5027 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5035 =
                                 let uu____5036 =
                                   let uu____5039 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____5039  in
                                 uu____5036.FStar_Syntax_Syntax.n  in
                               match uu____5035 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____5055))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5056 -> msg
                             else msg  in
                           let uu____5058 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5058
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5061 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5061 " is deprecated"  in
                           let uu____5062 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5062
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5063 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____5068 =
                      let uu____5069 =
                        let uu____5076 = mk_ref_read tm1  in
                        (uu____5076,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____5069  in
                    FStar_All.pipe_left mk1 uu____5068
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____5092 =
          let uu____5093 = unparen t  in uu____5093.FStar_Parser_AST.tm  in
        match uu____5092 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5094; FStar_Ident.ident = uu____5095;
              FStar_Ident.nsstr = uu____5096; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5099 ->
            let uu____5100 =
              let uu____5105 =
                let uu____5106 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5106  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5105)  in
            FStar_Errors.raise_error uu____5100 t.FStar_Parser_AST.range
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
          let uu___121_5195 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___121_5195.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___121_5195.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5198 =
          let uu____5199 = unparen top  in uu____5199.FStar_Parser_AST.tm  in
        match uu____5198 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5216 ->
            let uu____5223 = desugar_formula env top  in (uu____5223, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____5240 = desugar_formula env t  in (uu____5240, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____5257 = desugar_formula env t  in (uu____5257, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____5291 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____5291, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5303 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____5303, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____5325 =
                let uu____5326 =
                  let uu____5333 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____5333, args)  in
                FStar_Parser_AST.Op uu____5326  in
              FStar_Parser_AST.mk_term uu____5325 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____5336 =
              let uu____5337 =
                let uu____5338 =
                  let uu____5345 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____5345, [e])  in
                FStar_Parser_AST.Op uu____5338  in
              FStar_Parser_AST.mk_term uu____5337 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____5336
        | FStar_Parser_AST.Op (op_star,uu____5349::uu____5350::[]) when
            (let uu____5355 = FStar_Ident.text_of_id op_star  in
             uu____5355 = "*") &&
              (let uu____5357 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5357 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5370;_},t1::t2::[])
                  ->
                  let uu____5375 = flatten1 t1  in
                  FStar_List.append uu____5375 [t2]
              | uu____5378 -> [t]  in
            let uu____5379 =
              let uu____5388 =
                let uu____5395 =
                  let uu____5398 = unparen top  in flatten1 uu____5398  in
                FStar_All.pipe_right uu____5395
                  (FStar_List.map
                     (fun t  ->
                        let uu____5417 = desugar_typ_aq env t  in
                        match uu____5417 with
                        | (t',aq) ->
                            let uu____5428 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5428, aq)))
                 in
              FStar_All.pipe_right uu____5388 FStar_List.unzip  in
            (match uu____5379 with
             | (targs,aqs) ->
                 let uu____5457 =
                   let uu____5462 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5462
                    in
                 (match uu____5457 with
                  | (tup,uu____5472) ->
                      let uu____5473 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5473, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5491 =
              let uu____5494 =
                let uu____5497 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5497  in
              FStar_All.pipe_left setpos uu____5494  in
            (uu____5491, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5523 =
              let uu____5528 =
                let uu____5529 =
                  let uu____5530 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____5530 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____5529  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5528)  in
            FStar_Errors.raise_error uu____5523 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5541 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5541 with
             | FStar_Pervasives_Native.None  ->
                 let uu____5548 =
                   let uu____5553 =
                     let uu____5554 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5554
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5553)
                    in
                 FStar_Errors.raise_error uu____5548
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5564 =
                     let uu____5579 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____5621 = desugar_term_aq env t  in
                               match uu____5621 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____5579 FStar_List.unzip  in
                   (match uu____5564 with
                    | (args1,aqs) ->
                        let uu____5704 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____5704, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____5740)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____5755 =
              let uu___122_5756 = top  in
              let uu____5757 =
                let uu____5758 =
                  let uu____5765 =
                    let uu___123_5766 = top  in
                    let uu____5767 =
                      let uu____5768 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____5768  in
                    {
                      FStar_Parser_AST.tm = uu____5767;
                      FStar_Parser_AST.range =
                        (uu___123_5766.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___123_5766.FStar_Parser_AST.level)
                    }  in
                  (uu____5765, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____5758  in
              {
                FStar_Parser_AST.tm = uu____5757;
                FStar_Parser_AST.range =
                  (uu___122_5756.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___122_5756.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____5755
        | FStar_Parser_AST.Construct (n1,(a,uu____5771)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____5787 =
                let uu___124_5788 = top  in
                let uu____5789 =
                  let uu____5790 =
                    let uu____5797 =
                      let uu___125_5798 = top  in
                      let uu____5799 =
                        let uu____5800 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____5800  in
                      {
                        FStar_Parser_AST.tm = uu____5799;
                        FStar_Parser_AST.range =
                          (uu___125_5798.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___125_5798.FStar_Parser_AST.level)
                      }  in
                    (uu____5797, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____5790  in
                {
                  FStar_Parser_AST.tm = uu____5789;
                  FStar_Parser_AST.range =
                    (uu___124_5788.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___124_5788.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____5787))
        | FStar_Parser_AST.Construct (n1,(a,uu____5803)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____5818 =
              let uu___126_5819 = top  in
              let uu____5820 =
                let uu____5821 =
                  let uu____5828 =
                    let uu___127_5829 = top  in
                    let uu____5830 =
                      let uu____5831 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____5831  in
                    {
                      FStar_Parser_AST.tm = uu____5830;
                      FStar_Parser_AST.range =
                        (uu___127_5829.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___127_5829.FStar_Parser_AST.level)
                    }  in
                  (uu____5828, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____5821  in
              {
                FStar_Parser_AST.tm = uu____5820;
                FStar_Parser_AST.range =
                  (uu___126_5819.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___126_5819.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____5818
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5832; FStar_Ident.ident = uu____5833;
              FStar_Ident.nsstr = uu____5834; FStar_Ident.str = "Type0";_}
            ->
            let uu____5837 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____5837, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5852; FStar_Ident.ident = uu____5853;
              FStar_Ident.nsstr = uu____5854; FStar_Ident.str = "Type";_}
            ->
            let uu____5857 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____5857, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____5872; FStar_Ident.ident = uu____5873;
               FStar_Ident.nsstr = uu____5874; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5892 =
              let uu____5895 =
                let uu____5896 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____5896  in
              mk1 uu____5895  in
            (uu____5892, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5909; FStar_Ident.ident = uu____5910;
              FStar_Ident.nsstr = uu____5911; FStar_Ident.str = "Effect";_}
            ->
            let uu____5914 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____5914, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5929; FStar_Ident.ident = uu____5930;
              FStar_Ident.nsstr = uu____5931; FStar_Ident.str = "True";_}
            ->
            let uu____5934 =
              let uu____5935 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____5935
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____5934, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5946; FStar_Ident.ident = uu____5947;
              FStar_Ident.nsstr = uu____5948; FStar_Ident.str = "False";_}
            ->
            let uu____5951 =
              let uu____5952 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____5952
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____5951, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5965;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5967 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____5967 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____5976 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_defined_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____5976, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____5987 =
                    let uu____5988 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____5988 txt
                     in
                  failwith uu____5987))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5995 = desugar_name mk1 setpos env true l  in
              (uu____5995, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6008 = desugar_name mk1 setpos env true l  in
              (uu____6008, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____6029 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____6029 with
                | FStar_Pervasives_Native.Some uu____6038 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____6043 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____6043 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6057 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____6074 =
                    let uu____6075 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____6075  in
                  (uu____6074, noaqs)
              | uu____6086 ->
                  let uu____6093 =
                    let uu____6098 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6098)  in
                  FStar_Errors.raise_error uu____6093
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6105 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____6105 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6112 =
                    let uu____6117 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6117)
                     in
                  FStar_Errors.raise_error uu____6112
                    top.FStar_Parser_AST.range
              | uu____6122 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____6126 = desugar_name mk1 setpos env true lid'  in
                  (uu____6126, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6152 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6152 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6183 ->
                       let uu____6190 =
                         FStar_Util.take
                           (fun uu____6214  ->
                              match uu____6214 with
                              | (uu____6219,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____6190 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____6264 =
                              let uu____6279 =
                                FStar_List.map
                                  (fun uu____6312  ->
                                     match uu____6312 with
                                     | (t,imp) ->
                                         let uu____6329 =
                                           desugar_term_aq env t  in
                                         (match uu____6329 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____6279
                                FStar_List.unzip
                               in
                            (match uu____6264 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____6422 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____6422, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____6452 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____6452 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6459 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6470 =
              FStar_List.fold_left
                (fun uu____6515  ->
                   fun b  ->
                     match uu____6515 with
                     | (env1,tparams,typs) ->
                         let uu____6572 = desugar_binder env1 b  in
                         (match uu____6572 with
                          | (xopt,t1) ->
                              let uu____6601 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6610 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6610)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6601 with
                               | (env2,x) ->
                                   let uu____6630 =
                                     let uu____6633 =
                                       let uu____6636 =
                                         let uu____6637 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____6637
                                          in
                                       [uu____6636]  in
                                     FStar_List.append typs uu____6633  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___128_6663 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___128_6663.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___128_6663.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6630)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6470 with
             | (env1,uu____6691,targs) ->
                 let uu____6713 =
                   let uu____6718 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____6718
                    in
                 (match uu____6713 with
                  | (tup,uu____6728) ->
                      let uu____6729 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____6729, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____6754 = uncurry binders t  in
            (match uu____6754 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___94_6790 =
                   match uu___94_6790 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____6804 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____6804
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____6826 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____6826 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____6835 = aux env [] bs  in (uu____6835, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____6856 = desugar_binder env b  in
            (match uu____6856 with
             | (FStar_Pervasives_Native.None ,uu____6867) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____6881 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____6881 with
                  | ((x,uu____6891),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____6898 =
                        let uu____6901 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____6901  in
                      (uu____6898, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____6933 =
              FStar_List.fold_left
                (fun uu____6953  ->
                   fun pat  ->
                     match uu____6953 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____6979,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____6989 =
                                let uu____6992 = free_type_vars env1 t  in
                                FStar_List.append uu____6992 ftvs  in
                              (env1, uu____6989)
                          | FStar_Parser_AST.PatAscribed
                              (uu____6997,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____7008 =
                                let uu____7011 = free_type_vars env1 t  in
                                let uu____7014 =
                                  let uu____7017 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____7017 ftvs  in
                                FStar_List.append uu____7011 uu____7014  in
                              (env1, uu____7008)
                          | uu____7022 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____6933 with
             | (uu____7031,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____7043 =
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
                   FStar_List.append uu____7043 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___95_7088 =
                   match uu___95_7088 with
                   | [] ->
                       let uu____7111 = desugar_term_aq env1 body  in
                       (match uu____7111 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7142 =
                                      let uu____7143 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7143
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7142 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7196 =
                              let uu____7199 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7199  in
                            (uu____7196, aq))
                   | p::rest ->
                       let uu____7212 = desugar_binding_pat env1 p  in
                       (match uu____7212 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7240 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7245 =
                              match b with
                              | LetBinder uu____7278 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7334) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7370 =
                                          let uu____7375 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7375, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7370
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7411,uu____7412) ->
                                             let tup2 =
                                               let uu____7414 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7414
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7418 =
                                                 let uu____7421 =
                                                   let uu____7422 =
                                                     let uu____7437 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7440 =
                                                       let uu____7443 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7444 =
                                                         let uu____7447 =
                                                           let uu____7448 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7448
                                                            in
                                                         [uu____7447]  in
                                                       uu____7443 ::
                                                         uu____7444
                                                        in
                                                     (uu____7437, uu____7440)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7422
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7421
                                                  in
                                               uu____7418
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____7459 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7459
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____7490,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____7492,pats)) ->
                                             let tupn =
                                               let uu____7531 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7531
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7541 =
                                                 let uu____7542 =
                                                   let uu____7557 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____7560 =
                                                     let uu____7569 =
                                                       let uu____7578 =
                                                         let uu____7579 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7579
                                                          in
                                                       [uu____7578]  in
                                                     FStar_List.append args
                                                       uu____7569
                                                      in
                                                   (uu____7557, uu____7560)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____7542
                                                  in
                                               mk1 uu____7541  in
                                             let p2 =
                                               let uu____7599 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____7599
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____7634 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7245 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____7705,uu____7706,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____7724 =
                let uu____7725 = unparen e  in uu____7725.FStar_Parser_AST.tm
                 in
              match uu____7724 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____7735 ->
                  let uu____7736 = desugar_term_aq env e  in
                  (match uu____7736 with
                   | (head1,aq) ->
                       let uu____7749 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____7749, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____7756 ->
            let rec aux args aqs e =
              let uu____7809 =
                let uu____7810 = unparen e  in uu____7810.FStar_Parser_AST.tm
                 in
              match uu____7809 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____7830 = desugar_term_aq env t  in
                  (match uu____7830 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____7866 ->
                  let uu____7867 = desugar_term_aq env e  in
                  (match uu____7867 with
                   | (head1,aq) ->
                       let uu____7890 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____7890, (join_aqs (aq :: aqs))))
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
            let uu____7930 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____7930
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
            let uu____7982 = desugar_term_aq env t  in
            (match uu____7982 with
             | (tm,s) ->
                 let uu____7993 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____7993, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____8001 =
              let uu____8010 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____8010 then desugar_typ_aq else desugar_term_aq  in
            uu____8001 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8061 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8204  ->
                        match uu____8204 with
                        | (attr_opt,(p,def)) ->
                            let uu____8262 = is_app_pattern p  in
                            if uu____8262
                            then
                              let uu____8293 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8293, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____8375 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____8375, def1)
                               | uu____8420 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____8458);
                                           FStar_Parser_AST.prange =
                                             uu____8459;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____8507 =
                                            let uu____8528 =
                                              let uu____8533 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8533  in
                                            (uu____8528, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____8507, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____8624) ->
                                        if top_level
                                        then
                                          let uu____8659 =
                                            let uu____8680 =
                                              let uu____8685 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8685  in
                                            (uu____8680, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____8659, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____8775 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____8806 =
                FStar_List.fold_left
                  (fun uu____8879  ->
                     fun uu____8880  ->
                       match (uu____8879, uu____8880) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____8988,uu____8989),uu____8990))
                           ->
                           let uu____9107 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9133 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9133 with
                                  | (env2,xx) ->
                                      let uu____9152 =
                                        let uu____9155 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9155 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9152))
                             | FStar_Util.Inr l ->
                                 let uu____9163 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____9163, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9107 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____8806 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9305 =
                    match uu____9305 with
                    | (attrs_opt,(uu____9341,args,result_t),def) ->
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
                                let uu____9429 = is_comp_type env1 t  in
                                if uu____9429
                                then
                                  ((let uu____9431 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____9441 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____9441))
                                       in
                                    match uu____9431 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____9444 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____9446 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____9446))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____9444
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____9450 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____9450 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____9454 ->
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
                              let uu____9469 =
                                let uu____9470 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____9470
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____9469
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
                  let uu____9529 = desugar_term_aq env' body  in
                  (match uu____9529 with
                   | (body1,aq) ->
                       let uu____9542 =
                         let uu____9545 =
                           let uu____9546 =
                             let uu____9559 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____9559)  in
                           FStar_Syntax_Syntax.Tm_let uu____9546  in
                         FStar_All.pipe_left mk1 uu____9545  in
                       (uu____9542, aq))
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
              let uu____9619 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____9619 with
              | (env1,binder,pat1) ->
                  let uu____9641 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____9667 = desugar_term_aq env1 t2  in
                        (match uu____9667 with
                         | (body1,aq) ->
                             let fv =
                               let uu____9681 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____9681
                                 FStar_Pervasives_Native.None
                                in
                             let uu____9682 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____9682, aq))
                    | LocalBinder (x,uu____9706) ->
                        let uu____9707 = desugar_term_aq env1 t2  in
                        (match uu____9707 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____9721;
                                   FStar_Syntax_Syntax.p = uu____9722;_}::[]
                                   -> body1
                               | uu____9727 ->
                                   let uu____9730 =
                                     let uu____9733 =
                                       let uu____9734 =
                                         let uu____9757 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____9758 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____9757, uu____9758)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____9734
                                        in
                                     FStar_Syntax_Syntax.mk uu____9733  in
                                   uu____9730 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____9768 =
                               let uu____9771 =
                                 let uu____9772 =
                                   let uu____9785 =
                                     let uu____9786 =
                                       let uu____9787 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____9787]  in
                                     FStar_Syntax_Subst.close uu____9786
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____9785)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____9772  in
                               FStar_All.pipe_left mk1 uu____9771  in
                             (uu____9768, aq))
                     in
                  (match uu____9641 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____9828 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____9828, aq)
                       else (tm, aq))
               in
            let uu____9840 = FStar_List.hd lbs  in
            (match uu____9840 with
             | (attrs,(head_pat,defn)) ->
                 let uu____9884 = is_rec || (is_app_pattern head_pat)  in
                 if uu____9884
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____9897 =
                let uu____9898 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____9898  in
              mk1 uu____9897  in
            let uu____9899 = desugar_term_aq env t1  in
            (match uu____9899 with
             | (t1',aq1) ->
                 let uu____9910 = desugar_term_aq env t2  in
                 (match uu____9910 with
                  | (t2',aq2) ->
                      let uu____9921 = desugar_term_aq env t3  in
                      (match uu____9921 with
                       | (t3',aq3) ->
                           let uu____9932 =
                             let uu____9935 =
                               let uu____9936 =
                                 let uu____9959 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None)
                                    in
                                 let uu____9980 =
                                   let uu____9995 =
                                     let uu____10008 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____10008,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____10019 =
                                     let uu____10034 =
                                       let uu____10047 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____10047,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____10034]  in
                                   uu____9995 :: uu____10019  in
                                 (uu____9959, uu____9980)  in
                               FStar_Syntax_Syntax.Tm_match uu____9936  in
                             mk1 uu____9935  in
                           (uu____9932, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10206 =
              match uu____10206 with
              | (pat,wopt,b) ->
                  let uu____10228 = desugar_match_pat env pat  in
                  (match uu____10228 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____10253 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____10253
                          in
                       let uu____10254 = desugar_term_aq env1 b  in
                       (match uu____10254 with
                        | (b1,aq) ->
                            let uu____10267 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____10267, aq)))
               in
            let uu____10272 = desugar_term_aq env e  in
            (match uu____10272 with
             | (e1,aq) ->
                 let uu____10283 =
                   let uu____10292 =
                     let uu____10303 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____10303 FStar_List.unzip  in
                   FStar_All.pipe_right uu____10292
                     (fun uu____10367  ->
                        match uu____10367 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____10283 with
                  | (brs,aqs) ->
                      let uu____10418 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____10418, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____10451 = is_comp_type env t  in
              if uu____10451
              then
                let uu____10458 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____10458
              else
                (let uu____10464 = desugar_term env t  in
                 FStar_Util.Inl uu____10464)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____10470 = desugar_term_aq env e  in
            (match uu____10470 with
             | (e1,aq) ->
                 let uu____10481 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____10481, aq))
        | FStar_Parser_AST.Record (uu____10510,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____10551 = FStar_List.hd fields  in
              match uu____10551 with | (f,uu____10563) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____10605  ->
                        match uu____10605 with
                        | (g,uu____10611) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____10617,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____10631 =
                         let uu____10636 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____10636)
                          in
                       FStar_Errors.raise_error uu____10631
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
                  let uu____10644 =
                    let uu____10655 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____10686  ->
                              match uu____10686 with
                              | (f,uu____10696) ->
                                  let uu____10697 =
                                    let uu____10698 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____10698
                                     in
                                  (uu____10697, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____10655)  in
                  FStar_Parser_AST.Construct uu____10644
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____10716 =
                      let uu____10717 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____10717  in
                    FStar_Parser_AST.mk_term uu____10716
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____10719 =
                      let uu____10732 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____10762  ->
                                match uu____10762 with
                                | (f,uu____10772) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____10732)  in
                    FStar_Parser_AST.Record uu____10719  in
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
            let uu____10832 = desugar_term_aq env recterm1  in
            (match uu____10832 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____10848;
                         FStar_Syntax_Syntax.vars = uu____10849;_},args)
                      ->
                      let uu____10871 =
                        let uu____10874 =
                          let uu____10875 =
                            let uu____10890 =
                              let uu____10891 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____10892 =
                                let uu____10895 =
                                  let uu____10896 =
                                    let uu____10903 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____10903)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____10896
                                   in
                                FStar_Pervasives_Native.Some uu____10895  in
                              FStar_Syntax_Syntax.fvar uu____10891
                                FStar_Syntax_Syntax.Delta_constant
                                uu____10892
                               in
                            (uu____10890, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____10875  in
                        FStar_All.pipe_left mk1 uu____10874  in
                      (uu____10871, s)
                  | uu____10932 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____10936 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____10936 with
              | (constrname,is_rec) ->
                  let uu____10951 = desugar_term_aq env e  in
                  (match uu____10951 with
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
                       let uu____10969 =
                         let uu____10972 =
                           let uu____10973 =
                             let uu____10988 =
                               let uu____10989 =
                                 let uu____10990 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____10990
                                  in
                               FStar_Syntax_Syntax.fvar uu____10989
                                 FStar_Syntax_Syntax.Delta_equational qual
                                in
                             let uu____10991 =
                               let uu____10994 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____10994]  in
                             (uu____10988, uu____10991)  in
                           FStar_Syntax_Syntax.Tm_app uu____10973  in
                         FStar_All.pipe_left mk1 uu____10972  in
                       (uu____10969, s))))
        | FStar_Parser_AST.NamedTyp (uu____11001,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____11010 =
              let uu____11011 = FStar_Syntax_Subst.compress tm  in
              uu____11011.FStar_Syntax_Syntax.n  in
            (match uu____11010 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____11019 =
                   let uu___129_11022 =
                     let uu____11023 =
                       let uu____11024 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____11024  in
                     FStar_Syntax_Util.exp_string uu____11023  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___129_11022.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___129_11022.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____11019, noaqs)
             | uu____11037 ->
                 let uu____11038 =
                   let uu____11043 =
                     let uu____11044 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____11044
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____11043)  in
                 FStar_Errors.raise_error uu____11038
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____11050 = desugar_term_aq env e  in
            (match uu____11050 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____11062 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____11062, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____11082 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____11083 =
              let uu____11092 =
                let uu____11099 = desugar_term env e  in (bv, b, uu____11099)
                 in
              [uu____11092]  in
            (uu____11082, uu____11083)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____11130 =
              let uu____11133 =
                let uu____11134 =
                  let uu____11141 = desugar_term env e  in (uu____11141, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____11134  in
              FStar_All.pipe_left mk1 uu____11133  in
            (uu____11130, noaqs)
        | uu____11156 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____11157 = desugar_formula env top  in
            (uu____11157, noaqs)
        | uu____11168 ->
            let uu____11169 =
              let uu____11174 =
                let uu____11175 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____11175  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____11174)  in
            FStar_Errors.raise_error uu____11169 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____11181 -> false
    | uu____11190 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____11196 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____11196 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____11200 -> false

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
           (fun uu____11237  ->
              match uu____11237 with
              | (a,imp) ->
                  let uu____11250 = desugar_term env a  in
                  arg_withimp_e imp uu____11250))

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
        let is_requires uu____11276 =
          match uu____11276 with
          | (t1,uu____11282) ->
              let uu____11283 =
                let uu____11284 = unparen t1  in
                uu____11284.FStar_Parser_AST.tm  in
              (match uu____11283 with
               | FStar_Parser_AST.Requires uu____11285 -> true
               | uu____11292 -> false)
           in
        let is_ensures uu____11300 =
          match uu____11300 with
          | (t1,uu____11306) ->
              let uu____11307 =
                let uu____11308 = unparen t1  in
                uu____11308.FStar_Parser_AST.tm  in
              (match uu____11307 with
               | FStar_Parser_AST.Ensures uu____11309 -> true
               | uu____11316 -> false)
           in
        let is_app head1 uu____11327 =
          match uu____11327 with
          | (t1,uu____11333) ->
              let uu____11334 =
                let uu____11335 = unparen t1  in
                uu____11335.FStar_Parser_AST.tm  in
              (match uu____11334 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____11337;
                      FStar_Parser_AST.level = uu____11338;_},uu____11339,uu____11340)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____11341 -> false)
           in
        let is_smt_pat uu____11349 =
          match uu____11349 with
          | (t1,uu____11355) ->
              let uu____11356 =
                let uu____11357 = unparen t1  in
                uu____11357.FStar_Parser_AST.tm  in
              (match uu____11356 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____11360);
                             FStar_Parser_AST.range = uu____11361;
                             FStar_Parser_AST.level = uu____11362;_},uu____11363)::uu____11364::[])
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
                             FStar_Parser_AST.range = uu____11403;
                             FStar_Parser_AST.level = uu____11404;_},uu____11405)::uu____11406::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____11431 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____11459 = head_and_args t1  in
          match uu____11459 with
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
                   let thunk_ens uu____11553 =
                     match uu____11553 with
                     | (e,i) ->
                         let uu____11564 = thunk_ens_ e  in (uu____11564, i)
                      in
                   let fail_lemma uu____11574 =
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
                         let uu____11654 =
                           let uu____11661 =
                             let uu____11668 = thunk_ens ens  in
                             [uu____11668; nil_pat]  in
                           req_true :: uu____11661  in
                         unit_tm :: uu____11654
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____11715 =
                           let uu____11722 =
                             let uu____11729 = thunk_ens ens  in
                             [uu____11729; nil_pat]  in
                           req :: uu____11722  in
                         unit_tm :: uu____11715
                     | ens::smtpat::[] when
                         (((let uu____11778 = is_requires ens  in
                            Prims.op_Negation uu____11778) &&
                             (let uu____11780 = is_smt_pat ens  in
                              Prims.op_Negation uu____11780))
                            &&
                            (let uu____11782 = is_decreases ens  in
                             Prims.op_Negation uu____11782))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____11783 =
                           let uu____11790 =
                             let uu____11797 = thunk_ens ens  in
                             [uu____11797; smtpat]  in
                           req_true :: uu____11790  in
                         unit_tm :: uu____11783
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____11844 =
                           let uu____11851 =
                             let uu____11858 = thunk_ens ens  in
                             [uu____11858; nil_pat; dec]  in
                           req_true :: uu____11851  in
                         unit_tm :: uu____11844
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____11918 =
                           let uu____11925 =
                             let uu____11932 = thunk_ens ens  in
                             [uu____11932; smtpat; dec]  in
                           req_true :: uu____11925  in
                         unit_tm :: uu____11918
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____11992 =
                           let uu____11999 =
                             let uu____12006 = thunk_ens ens  in
                             [uu____12006; nil_pat; dec]  in
                           req :: uu____11999  in
                         unit_tm :: uu____11992
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12066 =
                           let uu____12073 =
                             let uu____12080 = thunk_ens ens  in
                             [uu____12080; smtpat]  in
                           req :: uu____12073  in
                         unit_tm :: uu____12066
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____12145 =
                           let uu____12152 =
                             let uu____12159 = thunk_ens ens  in
                             [uu____12159; dec; smtpat]  in
                           req :: uu____12152  in
                         unit_tm :: uu____12145
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____12221 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____12221, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12249 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12249
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____12250 =
                     let uu____12257 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12257, [])  in
                   (uu____12250, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12275 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12275
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____12276 =
                     let uu____12283 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12283, [])  in
                   (uu____12276, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____12299 =
                     let uu____12306 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12306, [])  in
                   (uu____12299, [(t1, FStar_Parser_AST.Nothing)])
               | uu____12329 ->
                   let default_effect =
                     let uu____12331 = FStar_Options.ml_ish ()  in
                     if uu____12331
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____12334 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____12334
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____12336 =
                     let uu____12343 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12343, [])  in
                   (uu____12336, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____12366 = pre_process_comp_typ t  in
        match uu____12366 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____12415 =
                       let uu____12420 =
                         let uu____12421 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____12421
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____12420)
                        in
                     fail1 () uu____12415)
                else Obj.repr ());
             (let is_universe uu____12430 =
                match uu____12430 with
                | (uu____12435,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____12437 = FStar_Util.take is_universe args  in
              match uu____12437 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____12496  ->
                         match uu____12496 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____12503 =
                    let uu____12518 = FStar_List.hd args1  in
                    let uu____12527 = FStar_List.tl args1  in
                    (uu____12518, uu____12527)  in
                  (match uu____12503 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____12582 =
                         let is_decrease uu____12618 =
                           match uu____12618 with
                           | (t1,uu____12628) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____12638;
                                       FStar_Syntax_Syntax.vars = uu____12639;_},uu____12640::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____12671 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____12582 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____12785  ->
                                      match uu____12785 with
                                      | (t1,uu____12795) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____12804,(arg,uu____12806)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____12835 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____12848 -> false  in
                              (((is_empty () (Obj.magic decreases_clause)) &&
                                  (is_empty () (Obj.magic rest2)))
                                 && (is_empty () (Obj.magic cattributes)))
                                && (is_empty () (Obj.magic universes1))
                               in
                            let uu____12851 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____12851
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____12855 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____12855
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____12862 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____12862
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____12866 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____12866
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____12870 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____12870
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____12874 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____12874
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____12892 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____12892
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
                                                  let uu____12981 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____12981
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
                                            | uu____12996 -> pat  in
                                          let uu____12997 =
                                            let uu____13008 =
                                              let uu____13019 =
                                                let uu____13028 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____13028, aq)  in
                                              [uu____13019]  in
                                            ens :: uu____13008  in
                                          req :: uu____12997
                                      | uu____13069 -> rest2
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
        | uu____13091 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___130_13108 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___130_13108.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___130_13108.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___131_13142 = b  in
             {
               FStar_Parser_AST.b = (uu___131_13142.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___131_13142.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___131_13142.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____13201 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____13201)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____13214 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____13214 with
             | (env1,a1) ->
                 let a2 =
                   let uu___132_13224 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___132_13224.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___132_13224.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____13246 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____13260 =
                     let uu____13263 =
                       let uu____13264 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____13264]  in
                     no_annot_abs uu____13263 body2  in
                   FStar_All.pipe_left setpos uu____13260  in
                 let uu____13269 =
                   let uu____13270 =
                     let uu____13285 =
                       let uu____13286 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____13286
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____13287 =
                       let uu____13290 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____13290]  in
                     (uu____13285, uu____13287)  in
                   FStar_Syntax_Syntax.Tm_app uu____13270  in
                 FStar_All.pipe_left mk1 uu____13269)
        | uu____13295 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____13367 = q (rest, pats, body)  in
              let uu____13374 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____13367 uu____13374
                FStar_Parser_AST.Formula
               in
            let uu____13375 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____13375 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____13384 -> failwith "impossible"  in
      let uu____13387 =
        let uu____13388 = unparen f  in uu____13388.FStar_Parser_AST.tm  in
      match uu____13387 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____13395,uu____13396) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____13407,uu____13408) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13439 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____13439
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13475 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____13475
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____13518 -> desugar_term env f

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
      let uu____13523 =
        FStar_List.fold_left
          (fun uu____13559  ->
             fun b  ->
               match uu____13559 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___133_13611 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___133_13611.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___133_13611.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___133_13611.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____13628 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____13628 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___134_13648 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___134_13648.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___134_13648.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____13665 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____13523 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____13752 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____13752)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____13757 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____13757)
      | FStar_Parser_AST.TVariable x ->
          let uu____13761 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____13761)
      | FStar_Parser_AST.NoName t ->
          let uu____13769 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____13769)
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
               (fun uu___96_13802  ->
                  match uu___96_13802 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____13803 -> false))
           in
        let quals2 q =
          let uu____13814 =
            (let uu____13817 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____13817) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____13814
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____13831 = FStar_Ident.range_of_lid disc_name  in
                let uu____13832 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____13831;
                  FStar_Syntax_Syntax.sigquals = uu____13832;
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
            let uu____13863 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____13893  ->
                        match uu____13893 with
                        | (x,uu____13901) ->
                            let uu____13902 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____13902 with
                             | (field_name,uu____13910) ->
                                 let only_decl =
                                   ((let uu____13914 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____13914)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____13916 =
                                        let uu____13917 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____13917.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____13916)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____13931 =
                                       FStar_List.filter
                                         (fun uu___97_13935  ->
                                            match uu___97_13935 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____13936 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____13931
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___98_13949  ->
                                             match uu___98_13949 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____13950 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____13952 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____13952;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____13959 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____13959
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____13964 =
                                        let uu____13969 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____13969  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____13964;
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
                                      let uu____13973 =
                                        let uu____13974 =
                                          let uu____13981 =
                                            let uu____13984 =
                                              let uu____13985 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____13985
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____13984]  in
                                          ((false, [lb]), uu____13981)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____13974
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____13973;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____13863 FStar_List.flatten
  
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
            (lid,uu____14029,t,uu____14031,n1,uu____14033) when
            let uu____14038 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____14038 ->
            let uu____14039 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____14039 with
             | (formals,uu____14055) ->
                 (match formals with
                  | [] -> []
                  | uu____14078 ->
                      let filter_records uu___99_14090 =
                        match uu___99_14090 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____14093,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____14105 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____14107 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____14107 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____14117 = FStar_Util.first_N n1 formals  in
                      (match uu____14117 with
                       | (uu____14140,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____14166 -> []
  
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
                    let uu____14216 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____14216
                    then
                      let uu____14219 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____14219
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____14222 =
                      let uu____14227 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____14227  in
                    let uu____14228 =
                      let uu____14231 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____14231  in
                    let uu____14234 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____14222;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____14228;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____14234;
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
          let tycon_id uu___100_14281 =
            match uu___100_14281 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____14283,uu____14284) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____14294,uu____14295,uu____14296) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____14306,uu____14307,uu____14308) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____14338,uu____14339,uu____14340) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____14382) ->
                let uu____14383 =
                  let uu____14384 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14384  in
                FStar_Parser_AST.mk_term uu____14383 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____14386 =
                  let uu____14387 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14387  in
                FStar_Parser_AST.mk_term uu____14386 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____14389) ->
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
              | uu____14412 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____14418 =
                     let uu____14419 =
                       let uu____14426 = binder_to_term b  in
                       (out, uu____14426, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____14419  in
                   FStar_Parser_AST.mk_term uu____14418
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___101_14436 =
            match uu___101_14436 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____14492  ->
                       match uu____14492 with
                       | (x,t,uu____14503) ->
                           let uu____14508 =
                             let uu____14509 =
                               let uu____14514 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____14514, t)  in
                             FStar_Parser_AST.Annotated uu____14509  in
                           FStar_Parser_AST.mk_binder uu____14508
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____14516 =
                    let uu____14517 =
                      let uu____14518 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____14518  in
                    FStar_Parser_AST.mk_term uu____14517
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____14516 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____14522 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____14549  ->
                          match uu____14549 with
                          | (x,uu____14559,uu____14560) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____14522)
            | uu____14613 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___102_14644 =
            match uu___102_14644 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____14668 = typars_of_binders _env binders  in
                (match uu____14668 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____14714 =
                         let uu____14715 =
                           let uu____14716 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____14716  in
                         FStar_Parser_AST.mk_term uu____14715
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____14714 binders  in
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
            | uu____14729 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____14773 =
              FStar_List.fold_left
                (fun uu____14813  ->
                   fun uu____14814  ->
                     match (uu____14813, uu____14814) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____14905 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____14905 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____14773 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____15018 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____15018
                | uu____15019 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____15027 = desugar_abstract_tc quals env [] tc  in
              (match uu____15027 with
               | (uu____15040,uu____15041,se,uu____15043) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____15046,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____15063 =
                                 let uu____15064 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____15064  in
                               if uu____15063
                               then
                                 let uu____15065 =
                                   let uu____15070 =
                                     let uu____15071 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____15071
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____15070)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____15065
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
                           | uu____15078 ->
                               let uu____15079 =
                                 let uu____15082 =
                                   let uu____15083 =
                                     let uu____15096 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____15096)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____15083
                                    in
                                 FStar_Syntax_Syntax.mk uu____15082  in
                               uu____15079 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___135_15100 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___135_15100.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___135_15100.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___135_15100.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____15103 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____15106 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____15106
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____15121 = typars_of_binders env binders  in
              (match uu____15121 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15157 =
                           FStar_Util.for_some
                             (fun uu___103_15159  ->
                                match uu___103_15159 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____15160 -> false) quals
                            in
                         if uu____15157
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____15167 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___104_15171  ->
                               match uu___104_15171 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____15172 -> false))
                        in
                     if uu____15167
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____15181 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____15181
                     then
                       let uu____15184 =
                         let uu____15191 =
                           let uu____15192 = unparen t  in
                           uu____15192.FStar_Parser_AST.tm  in
                         match uu____15191 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____15213 =
                               match FStar_List.rev args with
                               | (last_arg,uu____15243)::args_rev ->
                                   let uu____15255 =
                                     let uu____15256 = unparen last_arg  in
                                     uu____15256.FStar_Parser_AST.tm  in
                                   (match uu____15255 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____15284 -> ([], args))
                               | uu____15293 -> ([], args)  in
                             (match uu____15213 with
                              | (cattributes,args1) ->
                                  let uu____15332 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____15332))
                         | uu____15343 -> (t, [])  in
                       match uu____15184 with
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
                                  (fun uu___105_15365  ->
                                     match uu___105_15365 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____15366 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____15377)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____15401 = tycon_record_as_variant trec  in
              (match uu____15401 with
               | (t,fs) ->
                   let uu____15418 =
                     let uu____15421 =
                       let uu____15422 =
                         let uu____15431 =
                           let uu____15434 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____15434  in
                         (uu____15431, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____15422  in
                     uu____15421 :: quals  in
                   desugar_tycon env d uu____15418 [t])
          | uu____15439::uu____15440 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____15601 = et  in
                match uu____15601 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____15826 ->
                         let trec = tc  in
                         let uu____15850 = tycon_record_as_variant trec  in
                         (match uu____15850 with
                          | (t,fs) ->
                              let uu____15909 =
                                let uu____15912 =
                                  let uu____15913 =
                                    let uu____15922 =
                                      let uu____15925 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____15925  in
                                    (uu____15922, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____15913
                                   in
                                uu____15912 :: quals1  in
                              collect_tcs uu____15909 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____16012 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16012 with
                          | (env2,uu____16072,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____16221 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16221 with
                          | (env2,uu____16281,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____16406 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____16453 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____16453 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___107_16964  ->
                             match uu___107_16964 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____17031,uu____17032);
                                    FStar_Syntax_Syntax.sigrng = uu____17033;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____17034;
                                    FStar_Syntax_Syntax.sigmeta = uu____17035;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17036;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____17097 =
                                     typars_of_binders env1 binders  in
                                   match uu____17097 with
                                   | (env2,tpars1) ->
                                       let uu____17128 =
                                         push_tparams env2 tpars1  in
                                       (match uu____17128 with
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
                                 let uu____17161 =
                                   let uu____17182 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____17182)
                                    in
                                 [uu____17161]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____17250);
                                    FStar_Syntax_Syntax.sigrng = uu____17251;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____17253;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17254;_},constrs,tconstr,quals1)
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
                                 let uu____17350 = push_tparams env1 tpars
                                    in
                                 (match uu____17350 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____17427  ->
                                             match uu____17427 with
                                             | (x,uu____17441) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____17449 =
                                        let uu____17478 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____17592  ->
                                                  match uu____17592 with
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
                                                        let uu____17648 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____17648
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
                                                                uu___106_17659
                                                                 ->
                                                                match uu___106_17659
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____17671
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____17679 =
                                                        let uu____17700 =
                                                          let uu____17701 =
                                                            let uu____17702 =
                                                              let uu____17717
                                                                =
                                                                let uu____17720
                                                                  =
                                                                  let uu____17723
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____17723
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____17720
                                                                 in
                                                              (name, univs1,
                                                                uu____17717,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____17702
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____17701;
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
                                                          uu____17700)
                                                         in
                                                      (name, uu____17679)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____17478
                                         in
                                      (match uu____17449 with
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
                             | uu____17962 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18094  ->
                             match uu____18094 with
                             | (name_doc,uu____18122,uu____18123) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18203  ->
                             match uu____18203 with
                             | (uu____18224,uu____18225,se) -> se))
                      in
                   let uu____18255 =
                     let uu____18262 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____18262 rng
                      in
                   (match uu____18255 with
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
                               (fun uu____18328  ->
                                  match uu____18328 with
                                  | (uu____18351,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____18402,tps,k,uu____18405,constrs)
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
                                  | uu____18424 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____18441  ->
                                 match uu____18441 with
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
      let uu____18476 =
        FStar_List.fold_left
          (fun uu____18499  ->
             fun b  ->
               match uu____18499 with
               | (env1,binders1) ->
                   let uu____18519 = desugar_binder env1 b  in
                   (match uu____18519 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18536 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____18536 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____18553 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____18476 with
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
          let uu____18598 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___108_18603  ->
                    match uu___108_18603 with
                    | FStar_Syntax_Syntax.Reflectable uu____18604 -> true
                    | uu____18605 -> false))
             in
          if uu____18598
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____18608 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____18608
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
                  let uu____18712 = desugar_binders monad_env eff_binders  in
                  match uu____18712 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____18733 =
                          let uu____18734 =
                            let uu____18741 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____18741  in
                          FStar_List.length uu____18734  in
                        uu____18733 = (Prims.parse_int "1")  in
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
                            (uu____18783,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____18785,uu____18786,uu____18787),uu____18788)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____18821 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____18822 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____18834 = name_of_eff_decl decl  in
                             FStar_List.mem uu____18834 mandatory_members)
                          eff_decls
                         in
                      (match uu____18822 with
                       | (mandatory_members_decls,actions) ->
                           let uu____18851 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____18880  ->
                                     fun decl  ->
                                       match uu____18880 with
                                       | (env2,out) ->
                                           let uu____18900 =
                                             desugar_decl env2 decl  in
                                           (match uu____18900 with
                                            | (env3,ses) ->
                                                let uu____18913 =
                                                  let uu____18916 =
                                                    FStar_List.hd ses  in
                                                  uu____18916 :: out  in
                                                (env3, uu____18913)))
                                  (env1, []))
                              in
                           (match uu____18851 with
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
                                              (uu____18984,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____18987,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____18988,
                                                                  (def,uu____18990)::
                                                                  (cps_type,uu____18992)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____18993;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____18994;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____19046 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19046 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19066 =
                                                     let uu____19067 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19068 =
                                                       let uu____19069 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19069
                                                        in
                                                     let uu____19074 =
                                                       let uu____19075 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19075
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19067;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19068;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____19074
                                                     }  in
                                                   (uu____19066, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____19082,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____19085,defn),doc1)::[])
                                              when for_free ->
                                              let uu____19120 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19120 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19140 =
                                                     let uu____19141 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19142 =
                                                       let uu____19143 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19143
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19141;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19142;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____19140, doc1))
                                          | uu____19150 ->
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
                                    let uu____19180 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____19180
                                     in
                                  let uu____19181 =
                                    let uu____19182 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____19182
                                     in
                                  ([], uu____19181)  in
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
                                      let uu____19199 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____19199)  in
                                    let uu____19206 =
                                      let uu____19207 =
                                        let uu____19208 =
                                          let uu____19209 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19209
                                           in
                                        let uu____19218 = lookup1 "return"
                                           in
                                        let uu____19219 = lookup1 "bind"  in
                                        let uu____19220 =
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
                                            uu____19208;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____19218;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____19219;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____19220
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____19207
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____19206;
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
                                         (fun uu___109_19226  ->
                                            match uu___109_19226 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____19227 -> true
                                            | uu____19228 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____19238 =
                                       let uu____19239 =
                                         let uu____19240 =
                                           lookup1 "return_wp"  in
                                         let uu____19241 = lookup1 "bind_wp"
                                            in
                                         let uu____19242 =
                                           lookup1 "if_then_else"  in
                                         let uu____19243 = lookup1 "ite_wp"
                                            in
                                         let uu____19244 = lookup1 "stronger"
                                            in
                                         let uu____19245 = lookup1 "close_wp"
                                            in
                                         let uu____19246 = lookup1 "assert_p"
                                            in
                                         let uu____19247 = lookup1 "assume_p"
                                            in
                                         let uu____19248 = lookup1 "null_wp"
                                            in
                                         let uu____19249 = lookup1 "trivial"
                                            in
                                         let uu____19250 =
                                           if rr
                                           then
                                             let uu____19251 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____19251
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____19267 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____19269 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____19271 =
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
                                             uu____19240;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____19241;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____19242;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____19243;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____19244;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____19245;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____19246;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____19247;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____19248;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____19249;
                                           FStar_Syntax_Syntax.repr =
                                             uu____19250;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____19267;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____19269;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____19271
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____19239
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____19238;
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
                                          fun uu____19297  ->
                                            match uu____19297 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____19311 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____19311
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
                let uu____19335 = desugar_binders env1 eff_binders  in
                match uu____19335 with
                | (env2,binders) ->
                    let uu____19354 =
                      let uu____19373 = head_and_args defn  in
                      match uu____19373 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____19418 ->
                                let uu____19419 =
                                  let uu____19424 =
                                    let uu____19425 =
                                      let uu____19426 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____19426 " not found"
                                       in
                                    Prims.strcat "Effect " uu____19425  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____19424)
                                   in
                                FStar_Errors.raise_error uu____19419
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____19428 =
                            match FStar_List.rev args with
                            | (last_arg,uu____19458)::args_rev ->
                                let uu____19470 =
                                  let uu____19471 = unparen last_arg  in
                                  uu____19471.FStar_Parser_AST.tm  in
                                (match uu____19470 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____19499 -> ([], args))
                            | uu____19508 -> ([], args)  in
                          (match uu____19428 with
                           | (cattributes,args1) ->
                               let uu____19559 = desugar_args env2 args1  in
                               let uu____19568 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____19559, uu____19568))
                       in
                    (match uu____19354 with
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
                          (let uu____19624 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____19624 with
                           | (ed_binders,uu____19638,ed_binders_opening) ->
                               let sub1 uu____19649 =
                                 match uu____19649 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____19663 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____19663 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____19667 =
                                       let uu____19668 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____19668)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____19667
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____19673 =
                                   let uu____19674 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____19674
                                    in
                                 let uu____19685 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____19686 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____19687 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____19688 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____19689 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____19690 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____19691 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____19692 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____19693 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____19694 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____19695 =
                                   let uu____19696 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____19696
                                    in
                                 let uu____19707 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____19708 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____19709 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____19717 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____19718 =
                                          let uu____19719 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19719
                                           in
                                        let uu____19730 =
                                          let uu____19731 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19731
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____19717;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____19718;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____19730
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
                                     uu____19673;
                                   FStar_Syntax_Syntax.ret_wp = uu____19685;
                                   FStar_Syntax_Syntax.bind_wp = uu____19686;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____19687;
                                   FStar_Syntax_Syntax.ite_wp = uu____19688;
                                   FStar_Syntax_Syntax.stronger = uu____19689;
                                   FStar_Syntax_Syntax.close_wp = uu____19690;
                                   FStar_Syntax_Syntax.assert_p = uu____19691;
                                   FStar_Syntax_Syntax.assume_p = uu____19692;
                                   FStar_Syntax_Syntax.null_wp = uu____19693;
                                   FStar_Syntax_Syntax.trivial = uu____19694;
                                   FStar_Syntax_Syntax.repr = uu____19695;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____19707;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____19708;
                                   FStar_Syntax_Syntax.actions = uu____19709;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____19744 =
                                     let uu____19745 =
                                       let uu____19752 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____19752
                                        in
                                     FStar_List.length uu____19745  in
                                   uu____19744 = (Prims.parse_int "1")  in
                                 let uu____19781 =
                                   let uu____19784 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____19784 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____19781;
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
                                             let uu____19804 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____19804
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____19806 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____19806
                                 then
                                   let reflect_lid =
                                     let uu____19810 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____19810
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
    let uu____19822 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____19822 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____19873 ->
              let uu____19874 =
                let uu____19875 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____19875
                 in
              Prims.strcat "\n  " uu____19874
          | uu____19876 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____19889  ->
               match uu____19889 with
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
          let uu____19907 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____19907
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____19909 =
          let uu____19918 = FStar_Syntax_Syntax.as_arg arg  in [uu____19918]
           in
        FStar_Syntax_Util.mk_app fv uu____19909

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____19925 = desugar_decl_noattrs env d  in
      match uu____19925 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____19945 = mk_comment_attr d  in uu____19945 :: attrs1  in
          let uu____19950 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___136_19956 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___136_19956.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___136_19956.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___136_19956.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___136_19956.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____19950)

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
      | FStar_Parser_AST.Fsdoc uu____19982 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____19998 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____19998, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____20037  ->
                 match uu____20037 with | (x,uu____20045) -> x) tcs
             in
          let uu____20050 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____20050 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____20072;
                    FStar_Parser_AST.prange = uu____20073;_},uu____20074)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____20083;
                    FStar_Parser_AST.prange = uu____20084;_},uu____20085)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____20100;
                         FStar_Parser_AST.prange = uu____20101;_},uu____20102);
                    FStar_Parser_AST.prange = uu____20103;_},uu____20104)::[]
                   -> false
               | (p,uu____20132)::[] ->
                   let uu____20141 = is_app_pattern p  in
                   Prims.op_Negation uu____20141
               | uu____20142 -> false)
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
            let uu____20215 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____20215 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____20227 =
                     let uu____20228 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____20228.FStar_Syntax_Syntax.n  in
                   match uu____20227 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____20236) ->
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
                         | uu____20269::uu____20270 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____20273 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___110_20288  ->
                                     match uu___110_20288 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____20291;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20292;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20293;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20294;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20295;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20296;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20297;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20309;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20310;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20311;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20312;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20313;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20314;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____20328 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____20359  ->
                                   match uu____20359 with
                                   | (uu____20372,(uu____20373,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____20328
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____20397 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____20397
                         then
                           let uu____20406 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___137_20420 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___138_20422 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___138_20422.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___138_20422.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___137_20420.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___137_20420.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___137_20420.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___137_20420.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___137_20420.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___137_20420.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____20406)
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
                   | uu____20457 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____20463 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____20482 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____20463 with
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
                       let uu___139_20518 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___139_20518.FStar_Parser_AST.prange)
                       }
                   | uu____20525 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___140_20532 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___140_20532.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___140_20532.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___140_20532.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____20564 id1 =
                   match uu____20564 with
                   | (env1,ses) ->
                       let main =
                         let uu____20585 =
                           let uu____20586 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____20586  in
                         FStar_Parser_AST.mk_term uu____20585
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
                       let uu____20636 = desugar_decl env1 id_decl  in
                       (match uu____20636 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____20654 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____20654 FStar_Util.set_elements
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
            let uu____20685 = close_fun env t  in
            desugar_term env uu____20685  in
          let quals1 =
            let uu____20689 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____20689
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____20695 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____20695;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____20707 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____20707 with
           | (t,uu____20721) ->
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
            let uu____20755 =
              let uu____20762 = FStar_Syntax_Syntax.null_binder t  in
              [uu____20762]  in
            let uu____20763 =
              let uu____20766 =
                let uu____20767 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____20767  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____20766
               in
            FStar_Syntax_Util.arrow uu____20755 uu____20763  in
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
            let uu____20830 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____20830 with
            | FStar_Pervasives_Native.None  ->
                let uu____20833 =
                  let uu____20838 =
                    let uu____20839 =
                      let uu____20840 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____20840 " not found"  in
                    Prims.strcat "Effect name " uu____20839  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____20838)  in
                FStar_Errors.raise_error uu____20833
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____20844 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____20886 =
                  let uu____20895 =
                    let uu____20902 = desugar_term env t  in
                    ([], uu____20902)  in
                  FStar_Pervasives_Native.Some uu____20895  in
                (uu____20886, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____20935 =
                  let uu____20944 =
                    let uu____20951 = desugar_term env wp  in
                    ([], uu____20951)  in
                  FStar_Pervasives_Native.Some uu____20944  in
                let uu____20960 =
                  let uu____20969 =
                    let uu____20976 = desugar_term env t  in
                    ([], uu____20976)  in
                  FStar_Pervasives_Native.Some uu____20969  in
                (uu____20935, uu____20960)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____21002 =
                  let uu____21011 =
                    let uu____21018 = desugar_term env t  in
                    ([], uu____21018)  in
                  FStar_Pervasives_Native.Some uu____21011  in
                (FStar_Pervasives_Native.None, uu____21002)
             in
          (match uu____20844 with
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
            let uu____21098 =
              let uu____21099 =
                let uu____21106 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____21106, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____21099  in
            {
              FStar_Syntax_Syntax.sigel = uu____21098;
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
      let uu____21130 =
        FStar_List.fold_left
          (fun uu____21150  ->
             fun d  ->
               match uu____21150 with
               | (env1,sigelts) ->
                   let uu____21170 = desugar_decl env1 d  in
                   (match uu____21170 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____21130 with
      | (env1,sigelts) ->
          let rec forward acc uu___112_21211 =
            match uu___112_21211 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____21225,FStar_Syntax_Syntax.Sig_let uu____21226) ->
                     let uu____21239 =
                       let uu____21242 =
                         let uu___141_21243 = se2  in
                         let uu____21244 =
                           let uu____21247 =
                             FStar_List.filter
                               (fun uu___111_21261  ->
                                  match uu___111_21261 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____21265;
                                           FStar_Syntax_Syntax.vars =
                                             uu____21266;_},uu____21267);
                                      FStar_Syntax_Syntax.pos = uu____21268;
                                      FStar_Syntax_Syntax.vars = uu____21269;_}
                                      when
                                      let uu____21292 =
                                        let uu____21293 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____21293
                                         in
                                      uu____21292 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____21294 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____21247
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___141_21243.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___141_21243.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___141_21243.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___141_21243.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____21244
                         }  in
                       uu____21242 :: se1 :: acc  in
                     forward uu____21239 sigelts1
                 | uu____21299 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____21307 = forward [] sigelts  in (env1, uu____21307)
  
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
          | (FStar_Pervasives_Native.None ,uu____21358) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____21362;
               FStar_Syntax_Syntax.exports = uu____21363;
               FStar_Syntax_Syntax.is_interface = uu____21364;_},FStar_Parser_AST.Module
             (current_lid,uu____21366)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____21374) ->
              let uu____21377 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____21377
           in
        let uu____21382 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____21418 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____21418, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____21435 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____21435, mname, decls, false)
           in
        match uu____21382 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____21465 = desugar_decls env2 decls  in
            (match uu____21465 with
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
          let uu____21519 =
            (FStar_Options.interactive ()) &&
              (let uu____21521 =
                 let uu____21522 =
                   let uu____21523 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____21523  in
                 FStar_Util.get_file_extension uu____21522  in
               FStar_List.mem uu____21521 ["fsti"; "fsi"])
             in
          if uu____21519 then as_interface m else m  in
        let uu____21527 = desugar_modul_common curmod env m1  in
        match uu____21527 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____21542 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____21558 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____21558 with
      | (env1,modul,pop_when_done) ->
          let uu____21572 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____21572 with
           | (env2,modul1) ->
               ((let uu____21584 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____21584
                 then
                   let uu____21585 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____21585
                 else ());
                (let uu____21587 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____21587, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____21601 = desugar_modul env modul  in
      match uu____21601 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____21628 = desugar_decls env decls  in
      match uu____21628 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____21666 = desugar_partial_modul modul env a_modul  in
        match uu____21666 with | (env1,modul1) -> (modul1, env1)
  
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_Syntax_DsEnv.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        Prims.unit FStar_Syntax_DsEnv.withenv)
  =
  fun m  ->
    fun mii  ->
      fun erase_univs  ->
        fun en  ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____21740 ->
                  let t =
                    let uu____21748 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____21748  in
                  let uu____21757 =
                    let uu____21758 = FStar_Syntax_Subst.compress t  in
                    uu____21758.FStar_Syntax_Syntax.n  in
                  (match uu____21757 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____21768,uu____21769)
                       -> bs1
                   | uu____21790 -> failwith "Impossible")
               in
            let uu____21797 =
              let uu____21804 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____21804
                FStar_Syntax_Syntax.t_unit
               in
            match uu____21797 with
            | (binders,uu____21806,binders_opening) ->
                let erase_term t =
                  let uu____21812 =
                    let uu____21813 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____21813  in
                  FStar_Syntax_Subst.close binders uu____21812  in
                let erase_tscheme uu____21829 =
                  match uu____21829 with
                  | (us,t) ->
                      let t1 =
                        let uu____21849 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____21849 t  in
                      let uu____21852 =
                        let uu____21853 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____21853  in
                      ([], uu____21852)
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
                    | uu____21882 ->
                        let bs =
                          let uu____21890 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____21890  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____21920 =
                          let uu____21921 =
                            let uu____21924 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____21924  in
                          uu____21921.FStar_Syntax_Syntax.n  in
                        (match uu____21920 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____21932,uu____21933) -> bs1
                         | uu____21954 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____21965 =
                      let uu____21966 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____21966  in
                    FStar_Syntax_Subst.close binders uu____21965  in
                  let uu___142_21967 = action  in
                  let uu____21968 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____21969 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___142_21967.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___142_21967.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____21968;
                    FStar_Syntax_Syntax.action_typ = uu____21969
                  }  in
                let uu___143_21970 = ed  in
                let uu____21971 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____21972 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____21973 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____21974 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____21975 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____21976 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____21977 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____21978 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____21979 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____21980 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____21981 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____21982 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____21983 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____21984 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____21985 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____21986 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___143_21970.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___143_21970.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____21971;
                  FStar_Syntax_Syntax.signature = uu____21972;
                  FStar_Syntax_Syntax.ret_wp = uu____21973;
                  FStar_Syntax_Syntax.bind_wp = uu____21974;
                  FStar_Syntax_Syntax.if_then_else = uu____21975;
                  FStar_Syntax_Syntax.ite_wp = uu____21976;
                  FStar_Syntax_Syntax.stronger = uu____21977;
                  FStar_Syntax_Syntax.close_wp = uu____21978;
                  FStar_Syntax_Syntax.assert_p = uu____21979;
                  FStar_Syntax_Syntax.assume_p = uu____21980;
                  FStar_Syntax_Syntax.null_wp = uu____21981;
                  FStar_Syntax_Syntax.trivial = uu____21982;
                  FStar_Syntax_Syntax.repr = uu____21983;
                  FStar_Syntax_Syntax.return_repr = uu____21984;
                  FStar_Syntax_Syntax.bind_repr = uu____21985;
                  FStar_Syntax_Syntax.actions = uu____21986;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___143_21970.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___144_21998 = se  in
                  let uu____21999 =
                    let uu____22000 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____22000  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____21999;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___144_21998.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___144_21998.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___144_21998.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___144_21998.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___145_22004 = se  in
                  let uu____22005 =
                    let uu____22006 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22006
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____22005;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___145_22004.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___145_22004.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___145_22004.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___145_22004.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____22008 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____22009 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____22009 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____22021 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____22021
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____22023 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____22023)
  