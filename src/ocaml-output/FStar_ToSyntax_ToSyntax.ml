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
        (let resolvex l e x =
           let uu____2803 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2803 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2817 ->
               let uu____2820 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____2820 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2912 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2928 =
                 let uu____2929 =
                   let uu____2930 =
                     let uu____2937 =
                       let uu____2938 =
                         let uu____2943 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2943, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2938  in
                     (uu____2937, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2930  in
                 {
                   FStar_Parser_AST.pat = uu____2929;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2928
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____2960 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____2961 = aux loc env1 p2  in
                 match uu____2961 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___114_3015 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___115_3020 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___115_3020.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___115_3020.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___114_3015.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___116_3022 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___117_3027 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___117_3027.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___117_3027.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___116_3022.FStar_Syntax_Syntax.p)
                           }
                       | uu____3028 when top -> p4
                       | uu____3029 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____3032 =
                       match binder with
                       | LetBinder uu____3045 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____3065 = close_fun env1 t  in
                             desugar_term env1 uu____3065  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____3067 -> true)
                            then
                              (let uu____3068 =
                                 let uu____3073 =
                                   let uu____3074 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____3075 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____3076 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3074 uu____3075 uu____3076
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3073)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3068)
                            else ();
                            (let uu____3078 = annot_pat_var p3 t1  in
                             (uu____3078,
                               (LocalBinder
                                  ((let uu___118_3084 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___118_3084.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___118_3084.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____3032 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3106 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3106, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3117 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3117, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3138 = resolvex loc env1 x  in
               (match uu____3138 with
                | (loc1,env2,xbv) ->
                    let uu____3160 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3160, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3181 = resolvex loc env1 x  in
               (match uu____3181 with
                | (loc1,env2,xbv) ->
                    let uu____3203 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3203, imp))
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
               let uu____3215 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3215, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3239;_},args)
               ->
               let uu____3245 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3286  ->
                        match uu____3286 with
                        | (loc1,env2,args1) ->
                            let uu____3334 = aux loc1 env2 arg  in
                            (match uu____3334 with
                             | (loc2,env3,uu____3363,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____3245 with
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
                    let uu____3433 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3433, false))
           | FStar_Parser_AST.PatApp uu____3450 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3472 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3505  ->
                        match uu____3505 with
                        | (loc1,env2,pats1) ->
                            let uu____3537 = aux loc1 env2 pat  in
                            (match uu____3537 with
                             | (loc2,env3,uu____3562,pat1,uu____3564) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3472 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3607 =
                        let uu____3610 =
                          let uu____3615 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3615  in
                        let uu____3616 =
                          let uu____3617 =
                            let uu____3630 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3630, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3617  in
                        FStar_All.pipe_left uu____3610 uu____3616  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3662 =
                               let uu____3663 =
                                 let uu____3676 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3676, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3663  in
                             FStar_All.pipe_left (pos_r r) uu____3662) pats1
                        uu____3607
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
               let uu____3720 =
                 FStar_List.fold_left
                   (fun uu____3760  ->
                      fun p2  ->
                        match uu____3760 with
                        | (loc1,env2,pats) ->
                            let uu____3809 = aux loc1 env2 p2  in
                            (match uu____3809 with
                             | (loc2,env3,uu____3838,pat,uu____3840) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3720 with
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
                    let uu____3935 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____3935 with
                     | (constr,uu____3957) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3960 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3962 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3962, false)))
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
                      (fun uu____4033  ->
                         match uu____4033 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4063  ->
                         match uu____4063 with
                         | (f,uu____4069) ->
                             let uu____4070 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4096  ->
                                       match uu____4096 with
                                       | (g,uu____4102) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____4070 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4107,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____4114 =
                   let uu____4115 =
                     let uu____4122 =
                       let uu____4123 =
                         let uu____4124 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____4124  in
                       FStar_Parser_AST.mk_pattern uu____4123
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____4122, args)  in
                   FStar_Parser_AST.PatApp uu____4115  in
                 FStar_Parser_AST.mk_pattern uu____4114
                   p1.FStar_Parser_AST.prange
                  in
               let uu____4127 = aux loc env1 app  in
               (match uu____4127 with
                | (env2,e,b,p2,uu____4156) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4184 =
                            let uu____4185 =
                              let uu____4198 =
                                let uu___119_4199 = fv  in
                                let uu____4200 =
                                  let uu____4203 =
                                    let uu____4204 =
                                      let uu____4211 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4211)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4204
                                     in
                                  FStar_Pervasives_Native.Some uu____4203  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___119_4199.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___119_4199.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4200
                                }  in
                              (uu____4198, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____4185  in
                          FStar_All.pipe_left pos uu____4184
                      | uu____4238 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4288 = aux' true loc env1 p2  in
               (match uu____4288 with
                | (loc1,env2,var,p3,uu____4315) ->
                    let uu____4320 =
                      FStar_List.fold_left
                        (fun uu____4352  ->
                           fun p4  ->
                             match uu____4352 with
                             | (loc2,env3,ps1) ->
                                 let uu____4385 = aux' true loc2 env3 p4  in
                                 (match uu____4385 with
                                  | (loc3,env4,uu____4410,p5,uu____4412) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____4320 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4463 ->
               let uu____4464 = aux' true loc env1 p1  in
               (match uu____4464 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4504 = aux_maybe_or env p  in
         match uu____4504 with
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
            let uu____4563 =
              let uu____4564 =
                let uu____4575 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4575,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4564  in
            (env, uu____4563, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4603 =
                  let uu____4604 =
                    let uu____4609 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4609, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4604  in
                mklet uu____4603
            | FStar_Parser_AST.PatVar (x,uu____4611) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4617);
                   FStar_Parser_AST.prange = uu____4618;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4638 =
                  let uu____4639 =
                    let uu____4650 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____4651 =
                      let uu____4658 = desugar_term env t  in
                      (uu____4658, tacopt1)  in
                    (uu____4650, uu____4651)  in
                  LetBinder uu____4639  in
                (env, uu____4638, [])
            | uu____4669 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4679 = desugar_data_pat env p is_mut  in
             match uu____4679 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4708;
                       FStar_Syntax_Syntax.p = uu____4709;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4714;
                       FStar_Syntax_Syntax.p = uu____4715;_}::[] -> []
                   | uu____4720 -> p1  in
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
  fun uu____4727  ->
    fun env  ->
      fun pat  ->
        let uu____4730 = desugar_data_pat env pat false  in
        match uu____4730 with | (env1,uu____4746,pat1) -> (env1, pat1)

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
      let uu____4765 = desugar_term_aq env e  in
      match uu____4765 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____4782 = desugar_typ_aq env e  in
      match uu____4782 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____4792  ->
        fun range  ->
          match uu____4792 with
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
              ((let uu____4802 =
                  let uu____4803 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4803  in
                if uu____4802
                then
                  let uu____4804 =
                    let uu____4809 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4809)  in
                  FStar_Errors.log_issue range uu____4804
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
                  let uu____4814 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____4814 range  in
                let lid1 =
                  let uu____4818 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____4818 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4828) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____4837 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____4837 range  in
                           let private_fv =
                             let uu____4839 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4839 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___120_4840 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___120_4840.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___120_4840.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4841 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4848 =
                        let uu____4853 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4853)
                         in
                      FStar_Errors.raise_error uu____4848 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4869 =
                  let uu____4872 =
                    let uu____4873 =
                      let uu____4888 =
                        let uu____4897 =
                          let uu____4904 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4904)  in
                        [uu____4897]  in
                      (lid1, uu____4888)  in
                    FStar_Syntax_Syntax.Tm_app uu____4873  in
                  FStar_Syntax_Syntax.mk uu____4872  in
                uu____4869 FStar_Pervasives_Native.None range))

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
            let uu____4943 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4943 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____4990;
                              FStar_Syntax_Syntax.vars = uu____4991;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5014 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5014 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5022 =
                                 let uu____5023 =
                                   let uu____5026 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____5026  in
                                 uu____5023.FStar_Syntax_Syntax.n  in
                               match uu____5022 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____5042))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5043 -> msg
                             else msg  in
                           let uu____5045 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5045
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5048 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5048 " is deprecated"  in
                           let uu____5049 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5049
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5050 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____5055 =
                      let uu____5056 =
                        let uu____5063 = mk_ref_read tm1  in
                        (uu____5063,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____5056  in
                    FStar_All.pipe_left mk1 uu____5055
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____5079 =
          let uu____5080 = unparen t  in uu____5080.FStar_Parser_AST.tm  in
        match uu____5079 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5081; FStar_Ident.ident = uu____5082;
              FStar_Ident.nsstr = uu____5083; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5086 ->
            let uu____5087 =
              let uu____5092 =
                let uu____5093 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5093  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5092)  in
            FStar_Errors.raise_error uu____5087 t.FStar_Parser_AST.range
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
          let uu___121_5182 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___121_5182.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___121_5182.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5185 =
          let uu____5186 = unparen top  in uu____5186.FStar_Parser_AST.tm  in
        match uu____5185 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5203 ->
            let uu____5210 = desugar_formula env top  in (uu____5210, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____5227 = desugar_formula env t  in (uu____5227, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____5244 = desugar_formula env t  in (uu____5244, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____5278 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____5278, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5290 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____5290, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____5312 =
                let uu____5313 =
                  let uu____5320 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____5320, args)  in
                FStar_Parser_AST.Op uu____5313  in
              FStar_Parser_AST.mk_term uu____5312 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____5323 =
              let uu____5324 =
                let uu____5325 =
                  let uu____5332 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____5332, [e])  in
                FStar_Parser_AST.Op uu____5325  in
              FStar_Parser_AST.mk_term uu____5324 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____5323
        | FStar_Parser_AST.Op (op_star,uu____5336::uu____5337::[]) when
            (let uu____5342 = FStar_Ident.text_of_id op_star  in
             uu____5342 = "*") &&
              (let uu____5344 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5344 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5357;_},t1::t2::[])
                  ->
                  let uu____5362 = flatten1 t1  in
                  FStar_List.append uu____5362 [t2]
              | uu____5365 -> [t]  in
            let uu____5366 =
              let uu____5375 =
                let uu____5382 =
                  let uu____5385 = unparen top  in flatten1 uu____5385  in
                FStar_All.pipe_right uu____5382
                  (FStar_List.map
                     (fun t  ->
                        let uu____5404 = desugar_typ_aq env t  in
                        match uu____5404 with
                        | (t',aq) ->
                            let uu____5415 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5415, aq)))
                 in
              FStar_All.pipe_right uu____5375 FStar_List.unzip  in
            (match uu____5366 with
             | (targs,aqs) ->
                 let uu____5444 =
                   let uu____5449 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5449
                    in
                 (match uu____5444 with
                  | (tup,uu____5459) ->
                      let uu____5460 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5460, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5478 =
              let uu____5481 =
                let uu____5484 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5484  in
              FStar_All.pipe_left setpos uu____5481  in
            (uu____5478, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5510 =
              let uu____5515 =
                let uu____5516 =
                  let uu____5517 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____5517 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____5516  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5515)  in
            FStar_Errors.raise_error uu____5510 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5528 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5528 with
             | FStar_Pervasives_Native.None  ->
                 let uu____5535 =
                   let uu____5540 =
                     let uu____5541 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5541
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5540)
                    in
                 FStar_Errors.raise_error uu____5535
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5551 =
                     let uu____5566 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____5608 = desugar_term_aq env t  in
                               match uu____5608 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____5566 FStar_List.unzip  in
                   (match uu____5551 with
                    | (args1,aqs) ->
                        let uu____5691 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____5691, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____5727)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____5742 =
              let uu___122_5743 = top  in
              let uu____5744 =
                let uu____5745 =
                  let uu____5752 =
                    let uu___123_5753 = top  in
                    let uu____5754 =
                      let uu____5755 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____5755  in
                    {
                      FStar_Parser_AST.tm = uu____5754;
                      FStar_Parser_AST.range =
                        (uu___123_5753.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___123_5753.FStar_Parser_AST.level)
                    }  in
                  (uu____5752, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____5745  in
              {
                FStar_Parser_AST.tm = uu____5744;
                FStar_Parser_AST.range =
                  (uu___122_5743.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___122_5743.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____5742
        | FStar_Parser_AST.Construct (n1,(a,uu____5758)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____5774 =
                let uu___124_5775 = top  in
                let uu____5776 =
                  let uu____5777 =
                    let uu____5784 =
                      let uu___125_5785 = top  in
                      let uu____5786 =
                        let uu____5787 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____5787  in
                      {
                        FStar_Parser_AST.tm = uu____5786;
                        FStar_Parser_AST.range =
                          (uu___125_5785.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___125_5785.FStar_Parser_AST.level)
                      }  in
                    (uu____5784, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____5777  in
                {
                  FStar_Parser_AST.tm = uu____5776;
                  FStar_Parser_AST.range =
                    (uu___124_5775.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___124_5775.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____5774))
        | FStar_Parser_AST.Construct (n1,(a,uu____5790)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____5805 =
              let uu___126_5806 = top  in
              let uu____5807 =
                let uu____5808 =
                  let uu____5815 =
                    let uu___127_5816 = top  in
                    let uu____5817 =
                      let uu____5818 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____5818  in
                    {
                      FStar_Parser_AST.tm = uu____5817;
                      FStar_Parser_AST.range =
                        (uu___127_5816.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___127_5816.FStar_Parser_AST.level)
                    }  in
                  (uu____5815, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____5808  in
              {
                FStar_Parser_AST.tm = uu____5807;
                FStar_Parser_AST.range =
                  (uu___126_5806.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___126_5806.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____5805
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5819; FStar_Ident.ident = uu____5820;
              FStar_Ident.nsstr = uu____5821; FStar_Ident.str = "Type0";_}
            ->
            let uu____5824 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____5824, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5839; FStar_Ident.ident = uu____5840;
              FStar_Ident.nsstr = uu____5841; FStar_Ident.str = "Type";_}
            ->
            let uu____5844 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____5844, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____5859; FStar_Ident.ident = uu____5860;
               FStar_Ident.nsstr = uu____5861; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5879 =
              let uu____5882 =
                let uu____5883 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____5883  in
              mk1 uu____5882  in
            (uu____5879, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5896; FStar_Ident.ident = uu____5897;
              FStar_Ident.nsstr = uu____5898; FStar_Ident.str = "Effect";_}
            ->
            let uu____5901 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____5901, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5916; FStar_Ident.ident = uu____5917;
              FStar_Ident.nsstr = uu____5918; FStar_Ident.str = "True";_}
            ->
            let uu____5921 =
              let uu____5922 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____5922
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____5921, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5933; FStar_Ident.ident = uu____5934;
              FStar_Ident.nsstr = uu____5935; FStar_Ident.str = "False";_}
            ->
            let uu____5938 =
              let uu____5939 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____5939
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____5938, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5952;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5954 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____5954 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____5963 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_defined_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____5963, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____5974 =
                    let uu____5975 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____5975 txt
                     in
                  failwith uu____5974))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5982 = desugar_name mk1 setpos env true l  in
              (uu____5982, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5995 = desugar_name mk1 setpos env true l  in
              (uu____5995, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____6016 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____6016 with
                | FStar_Pervasives_Native.Some uu____6025 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____6030 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____6030 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6044 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____6061 =
                    let uu____6062 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____6062  in
                  (uu____6061, noaqs)
              | uu____6073 ->
                  let uu____6080 =
                    let uu____6085 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6085)  in
                  FStar_Errors.raise_error uu____6080
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6092 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____6092 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6099 =
                    let uu____6104 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6104)
                     in
                  FStar_Errors.raise_error uu____6099
                    top.FStar_Parser_AST.range
              | uu____6109 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____6113 = desugar_name mk1 setpos env true lid'  in
                  (uu____6113, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6139 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6139 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6170 ->
                       let uu____6177 =
                         FStar_Util.take
                           (fun uu____6201  ->
                              match uu____6201 with
                              | (uu____6206,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____6177 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____6251 =
                              let uu____6266 =
                                FStar_List.map
                                  (fun uu____6299  ->
                                     match uu____6299 with
                                     | (t,imp) ->
                                         let uu____6316 =
                                           desugar_term_aq env t  in
                                         (match uu____6316 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____6266
                                FStar_List.unzip
                               in
                            (match uu____6251 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____6409 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____6409, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____6439 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____6439 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6446 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6457 =
              FStar_List.fold_left
                (fun uu____6502  ->
                   fun b  ->
                     match uu____6502 with
                     | (env1,tparams,typs) ->
                         let uu____6559 = desugar_binder env1 b  in
                         (match uu____6559 with
                          | (xopt,t1) ->
                              let uu____6588 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6597 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6597)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6588 with
                               | (env2,x) ->
                                   let uu____6617 =
                                     let uu____6620 =
                                       let uu____6623 =
                                         let uu____6624 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____6624
                                          in
                                       [uu____6623]  in
                                     FStar_List.append typs uu____6620  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___128_6650 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___128_6650.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___128_6650.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6617)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6457 with
             | (env1,uu____6678,targs) ->
                 let uu____6700 =
                   let uu____6705 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____6705
                    in
                 (match uu____6700 with
                  | (tup,uu____6715) ->
                      let uu____6716 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____6716, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____6741 = uncurry binders t  in
            (match uu____6741 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___94_6777 =
                   match uu___94_6777 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____6791 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____6791
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____6813 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____6813 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____6822 = aux env [] bs  in (uu____6822, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____6843 = desugar_binder env b  in
            (match uu____6843 with
             | (FStar_Pervasives_Native.None ,uu____6854) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____6868 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____6868 with
                  | ((x,uu____6878),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____6885 =
                        let uu____6888 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____6888  in
                      (uu____6885, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____6920 =
              FStar_List.fold_left
                (fun uu____6940  ->
                   fun pat  ->
                     match uu____6940 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____6966,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____6976 =
                                let uu____6979 = free_type_vars env1 t  in
                                FStar_List.append uu____6979 ftvs  in
                              (env1, uu____6976)
                          | FStar_Parser_AST.PatAscribed
                              (uu____6984,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____6995 =
                                let uu____6998 = free_type_vars env1 t  in
                                let uu____7001 =
                                  let uu____7004 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____7004 ftvs  in
                                FStar_List.append uu____6998 uu____7001  in
                              (env1, uu____6995)
                          | uu____7009 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____6920 with
             | (uu____7018,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____7030 =
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
                   FStar_List.append uu____7030 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___95_7075 =
                   match uu___95_7075 with
                   | [] ->
                       let uu____7098 = desugar_term_aq env1 body  in
                       (match uu____7098 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7129 =
                                      let uu____7130 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7130
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7129 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7183 =
                              let uu____7186 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7186  in
                            (uu____7183, aq))
                   | p::rest ->
                       let uu____7199 = desugar_binding_pat env1 p  in
                       (match uu____7199 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7227 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7232 =
                              match b with
                              | LetBinder uu____7265 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7321) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7357 =
                                          let uu____7362 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7362, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7357
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7398,uu____7399) ->
                                             let tup2 =
                                               let uu____7401 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7401
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7405 =
                                                 let uu____7408 =
                                                   let uu____7409 =
                                                     let uu____7424 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7427 =
                                                       let uu____7430 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7431 =
                                                         let uu____7434 =
                                                           let uu____7435 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7435
                                                            in
                                                         [uu____7434]  in
                                                       uu____7430 ::
                                                         uu____7431
                                                        in
                                                     (uu____7424, uu____7427)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7409
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7408
                                                  in
                                               uu____7405
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____7446 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7446
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____7477,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____7479,pats)) ->
                                             let tupn =
                                               let uu____7518 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7518
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7528 =
                                                 let uu____7529 =
                                                   let uu____7544 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____7547 =
                                                     let uu____7556 =
                                                       let uu____7565 =
                                                         let uu____7566 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7566
                                                          in
                                                       [uu____7565]  in
                                                     FStar_List.append args
                                                       uu____7556
                                                      in
                                                   (uu____7544, uu____7547)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____7529
                                                  in
                                               mk1 uu____7528  in
                                             let p2 =
                                               let uu____7586 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____7586
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____7621 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7232 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____7692,uu____7693,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____7711 =
                let uu____7712 = unparen e  in uu____7712.FStar_Parser_AST.tm
                 in
              match uu____7711 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____7722 ->
                  let uu____7723 = desugar_term_aq env e  in
                  (match uu____7723 with
                   | (head1,aq) ->
                       let uu____7736 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____7736, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____7743 ->
            let rec aux args aqs e =
              let uu____7796 =
                let uu____7797 = unparen e  in uu____7797.FStar_Parser_AST.tm
                 in
              match uu____7796 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____7817 = desugar_term_aq env t  in
                  (match uu____7817 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____7853 ->
                  let uu____7854 = desugar_term_aq env e  in
                  (match uu____7854 with
                   | (head1,aq) ->
                       let uu____7877 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____7877, (join_aqs (aq :: aqs))))
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
            let uu____7917 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____7917
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
            let uu____7969 = desugar_term_aq env t  in
            (match uu____7969 with
             | (tm,s) ->
                 let uu____7980 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____7980, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____7988 =
              let uu____7997 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____7997 then desugar_typ_aq else desugar_term_aq  in
            uu____7988 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8048 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8191  ->
                        match uu____8191 with
                        | (attr_opt,(p,def)) ->
                            let uu____8249 = is_app_pattern p  in
                            if uu____8249
                            then
                              let uu____8280 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8280, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____8362 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____8362, def1)
                               | uu____8407 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____8445);
                                           FStar_Parser_AST.prange =
                                             uu____8446;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____8494 =
                                            let uu____8515 =
                                              let uu____8520 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8520  in
                                            (uu____8515, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____8494, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____8611) ->
                                        if top_level
                                        then
                                          let uu____8646 =
                                            let uu____8667 =
                                              let uu____8672 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8672  in
                                            (uu____8667, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____8646, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____8762 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____8793 =
                FStar_List.fold_left
                  (fun uu____8866  ->
                     fun uu____8867  ->
                       match (uu____8866, uu____8867) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____8975,uu____8976),uu____8977))
                           ->
                           let uu____9094 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9120 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9120 with
                                  | (env2,xx) ->
                                      let uu____9139 =
                                        let uu____9142 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9142 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9139))
                             | FStar_Util.Inr l ->
                                 let uu____9150 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____9150, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9094 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____8793 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9292 =
                    match uu____9292 with
                    | (attrs_opt,(uu____9328,args,result_t),def) ->
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
                                let uu____9416 = is_comp_type env1 t  in
                                if uu____9416
                                then
                                  ((let uu____9418 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____9428 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____9428))
                                       in
                                    match uu____9418 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____9431 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____9433 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____9433))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____9431
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____9437 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____9437 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____9441 ->
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
                              let uu____9456 =
                                let uu____9457 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____9457
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____9456
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
                  let uu____9516 = desugar_term_aq env' body  in
                  (match uu____9516 with
                   | (body1,aq) ->
                       let uu____9529 =
                         let uu____9532 =
                           let uu____9533 =
                             let uu____9546 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____9546)  in
                           FStar_Syntax_Syntax.Tm_let uu____9533  in
                         FStar_All.pipe_left mk1 uu____9532  in
                       (uu____9529, aq))
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
              let uu____9606 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____9606 with
              | (env1,binder,pat1) ->
                  let uu____9628 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____9654 = desugar_term_aq env1 t2  in
                        (match uu____9654 with
                         | (body1,aq) ->
                             let fv =
                               let uu____9668 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____9668
                                 FStar_Pervasives_Native.None
                                in
                             let uu____9669 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____9669, aq))
                    | LocalBinder (x,uu____9693) ->
                        let uu____9694 = desugar_term_aq env1 t2  in
                        (match uu____9694 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____9708;
                                   FStar_Syntax_Syntax.p = uu____9709;_}::[]
                                   -> body1
                               | uu____9714 ->
                                   let uu____9717 =
                                     let uu____9720 =
                                       let uu____9721 =
                                         let uu____9744 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____9745 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____9744, uu____9745)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____9721
                                        in
                                     FStar_Syntax_Syntax.mk uu____9720  in
                                   uu____9717 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____9755 =
                               let uu____9758 =
                                 let uu____9759 =
                                   let uu____9772 =
                                     let uu____9773 =
                                       let uu____9774 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____9774]  in
                                     FStar_Syntax_Subst.close uu____9773
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____9772)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____9759  in
                               FStar_All.pipe_left mk1 uu____9758  in
                             (uu____9755, aq))
                     in
                  (match uu____9628 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____9815 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____9815, aq)
                       else (tm, aq))
               in
            let uu____9827 = FStar_List.hd lbs  in
            (match uu____9827 with
             | (attrs,(head_pat,defn)) ->
                 let uu____9871 = is_rec || (is_app_pattern head_pat)  in
                 if uu____9871
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____9884 =
                let uu____9885 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____9885  in
              mk1 uu____9884  in
            let uu____9886 = desugar_term_aq env t1  in
            (match uu____9886 with
             | (t1',aq1) ->
                 let uu____9897 = desugar_term_aq env t2  in
                 (match uu____9897 with
                  | (t2',aq2) ->
                      let uu____9908 = desugar_term_aq env t3  in
                      (match uu____9908 with
                       | (t3',aq3) ->
                           let uu____9919 =
                             let uu____9922 =
                               let uu____9923 =
                                 let uu____9946 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None)
                                    in
                                 let uu____9967 =
                                   let uu____9982 =
                                     let uu____9995 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____9995,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____10006 =
                                     let uu____10021 =
                                       let uu____10034 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____10034,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____10021]  in
                                   uu____9982 :: uu____10006  in
                                 (uu____9946, uu____9967)  in
                               FStar_Syntax_Syntax.Tm_match uu____9923  in
                             mk1 uu____9922  in
                           (uu____9919, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10193 =
              match uu____10193 with
              | (pat,wopt,b) ->
                  let uu____10215 = desugar_match_pat env pat  in
                  (match uu____10215 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____10240 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____10240
                          in
                       let uu____10241 = desugar_term_aq env1 b  in
                       (match uu____10241 with
                        | (b1,aq) ->
                            let uu____10254 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____10254, aq)))
               in
            let uu____10259 = desugar_term_aq env e  in
            (match uu____10259 with
             | (e1,aq) ->
                 let uu____10270 =
                   let uu____10279 =
                     let uu____10290 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____10290 FStar_List.unzip  in
                   FStar_All.pipe_right uu____10279
                     (fun uu____10354  ->
                        match uu____10354 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____10270 with
                  | (brs,aqs) ->
                      let uu____10405 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____10405, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____10438 = is_comp_type env t  in
              if uu____10438
              then
                let uu____10445 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____10445
              else
                (let uu____10451 = desugar_term env t  in
                 FStar_Util.Inl uu____10451)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____10457 = desugar_term_aq env e  in
            (match uu____10457 with
             | (e1,aq) ->
                 let uu____10468 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____10468, aq))
        | FStar_Parser_AST.Record (uu____10497,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____10538 = FStar_List.hd fields  in
              match uu____10538 with | (f,uu____10550) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____10592  ->
                        match uu____10592 with
                        | (g,uu____10598) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____10604,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____10618 =
                         let uu____10623 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____10623)
                          in
                       FStar_Errors.raise_error uu____10618
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
                  let uu____10631 =
                    let uu____10642 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____10673  ->
                              match uu____10673 with
                              | (f,uu____10683) ->
                                  let uu____10684 =
                                    let uu____10685 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____10685
                                     in
                                  (uu____10684, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____10642)  in
                  FStar_Parser_AST.Construct uu____10631
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____10703 =
                      let uu____10704 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____10704  in
                    FStar_Parser_AST.mk_term uu____10703
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____10706 =
                      let uu____10719 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____10749  ->
                                match uu____10749 with
                                | (f,uu____10759) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____10719)  in
                    FStar_Parser_AST.Record uu____10706  in
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
            let uu____10819 = desugar_term_aq env recterm1  in
            (match uu____10819 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____10835;
                         FStar_Syntax_Syntax.vars = uu____10836;_},args)
                      ->
                      let uu____10858 =
                        let uu____10861 =
                          let uu____10862 =
                            let uu____10877 =
                              let uu____10878 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____10879 =
                                let uu____10882 =
                                  let uu____10883 =
                                    let uu____10890 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____10890)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____10883
                                   in
                                FStar_Pervasives_Native.Some uu____10882  in
                              FStar_Syntax_Syntax.fvar uu____10878
                                FStar_Syntax_Syntax.Delta_constant
                                uu____10879
                               in
                            (uu____10877, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____10862  in
                        FStar_All.pipe_left mk1 uu____10861  in
                      (uu____10858, s)
                  | uu____10919 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____10923 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____10923 with
              | (constrname,is_rec) ->
                  let uu____10938 = desugar_term_aq env e  in
                  (match uu____10938 with
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
                       let uu____10956 =
                         let uu____10959 =
                           let uu____10960 =
                             let uu____10975 =
                               let uu____10976 =
                                 let uu____10977 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____10977
                                  in
                               FStar_Syntax_Syntax.fvar uu____10976
                                 FStar_Syntax_Syntax.Delta_equational qual
                                in
                             let uu____10978 =
                               let uu____10981 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____10981]  in
                             (uu____10975, uu____10978)  in
                           FStar_Syntax_Syntax.Tm_app uu____10960  in
                         FStar_All.pipe_left mk1 uu____10959  in
                       (uu____10956, s))))
        | FStar_Parser_AST.NamedTyp (uu____10988,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____10997 =
              let uu____10998 = FStar_Syntax_Subst.compress tm  in
              uu____10998.FStar_Syntax_Syntax.n  in
            (match uu____10997 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____11006 =
                   let uu___129_11009 =
                     let uu____11010 =
                       let uu____11011 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____11011  in
                     FStar_Syntax_Util.exp_string uu____11010  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___129_11009.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___129_11009.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____11006, noaqs)
             | uu____11024 ->
                 let uu____11025 =
                   let uu____11030 =
                     let uu____11031 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____11031
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____11030)  in
                 FStar_Errors.raise_error uu____11025
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____11037 = desugar_term_aq env e  in
            (match uu____11037 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____11049 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____11049, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____11069 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____11070 =
              let uu____11079 =
                let uu____11086 = desugar_term env e  in (bv, b, uu____11086)
                 in
              [uu____11079]  in
            (uu____11069, uu____11070)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____11117 =
              let uu____11120 =
                let uu____11121 =
                  let uu____11128 = desugar_term env e  in (uu____11128, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____11121  in
              FStar_All.pipe_left mk1 uu____11120  in
            (uu____11117, noaqs)
        | uu____11143 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____11144 = desugar_formula env top  in
            (uu____11144, noaqs)
        | uu____11155 ->
            let uu____11156 =
              let uu____11161 =
                let uu____11162 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____11162  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____11161)  in
            FStar_Errors.raise_error uu____11156 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____11168 -> false
    | uu____11177 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____11183 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____11183 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____11187 -> false

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
           (fun uu____11224  ->
              match uu____11224 with
              | (a,imp) ->
                  let uu____11237 = desugar_term env a  in
                  arg_withimp_e imp uu____11237))

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
        let is_requires uu____11263 =
          match uu____11263 with
          | (t1,uu____11269) ->
              let uu____11270 =
                let uu____11271 = unparen t1  in
                uu____11271.FStar_Parser_AST.tm  in
              (match uu____11270 with
               | FStar_Parser_AST.Requires uu____11272 -> true
               | uu____11279 -> false)
           in
        let is_ensures uu____11287 =
          match uu____11287 with
          | (t1,uu____11293) ->
              let uu____11294 =
                let uu____11295 = unparen t1  in
                uu____11295.FStar_Parser_AST.tm  in
              (match uu____11294 with
               | FStar_Parser_AST.Ensures uu____11296 -> true
               | uu____11303 -> false)
           in
        let is_app head1 uu____11314 =
          match uu____11314 with
          | (t1,uu____11320) ->
              let uu____11321 =
                let uu____11322 = unparen t1  in
                uu____11322.FStar_Parser_AST.tm  in
              (match uu____11321 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____11324;
                      FStar_Parser_AST.level = uu____11325;_},uu____11326,uu____11327)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____11328 -> false)
           in
        let is_smt_pat uu____11336 =
          match uu____11336 with
          | (t1,uu____11342) ->
              let uu____11343 =
                let uu____11344 = unparen t1  in
                uu____11344.FStar_Parser_AST.tm  in
              (match uu____11343 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____11347);
                             FStar_Parser_AST.range = uu____11348;
                             FStar_Parser_AST.level = uu____11349;_},uu____11350)::uu____11351::[])
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
                             FStar_Parser_AST.range = uu____11390;
                             FStar_Parser_AST.level = uu____11391;_},uu____11392)::uu____11393::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____11418 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____11446 = head_and_args t1  in
          match uu____11446 with
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
                   let thunk_ens uu____11540 =
                     match uu____11540 with
                     | (e,i) ->
                         let uu____11551 = thunk_ens_ e  in (uu____11551, i)
                      in
                   let fail_lemma uu____11561 =
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
                         let uu____11641 =
                           let uu____11648 =
                             let uu____11655 = thunk_ens ens  in
                             [uu____11655; nil_pat]  in
                           req_true :: uu____11648  in
                         unit_tm :: uu____11641
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____11702 =
                           let uu____11709 =
                             let uu____11716 = thunk_ens ens  in
                             [uu____11716; nil_pat]  in
                           req :: uu____11709  in
                         unit_tm :: uu____11702
                     | ens::smtpat::[] when
                         (((let uu____11765 = is_requires ens  in
                            Prims.op_Negation uu____11765) &&
                             (let uu____11767 = is_smt_pat ens  in
                              Prims.op_Negation uu____11767))
                            &&
                            (let uu____11769 = is_decreases ens  in
                             Prims.op_Negation uu____11769))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____11770 =
                           let uu____11777 =
                             let uu____11784 = thunk_ens ens  in
                             [uu____11784; smtpat]  in
                           req_true :: uu____11777  in
                         unit_tm :: uu____11770
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____11831 =
                           let uu____11838 =
                             let uu____11845 = thunk_ens ens  in
                             [uu____11845; nil_pat; dec]  in
                           req_true :: uu____11838  in
                         unit_tm :: uu____11831
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____11905 =
                           let uu____11912 =
                             let uu____11919 = thunk_ens ens  in
                             [uu____11919; smtpat; dec]  in
                           req_true :: uu____11912  in
                         unit_tm :: uu____11905
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____11979 =
                           let uu____11986 =
                             let uu____11993 = thunk_ens ens  in
                             [uu____11993; nil_pat; dec]  in
                           req :: uu____11986  in
                         unit_tm :: uu____11979
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12053 =
                           let uu____12060 =
                             let uu____12067 = thunk_ens ens  in
                             [uu____12067; smtpat]  in
                           req :: uu____12060  in
                         unit_tm :: uu____12053
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____12132 =
                           let uu____12139 =
                             let uu____12146 = thunk_ens ens  in
                             [uu____12146; dec; smtpat]  in
                           req :: uu____12139  in
                         unit_tm :: uu____12132
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____12208 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____12208, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12236 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12236
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____12237 =
                     let uu____12244 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12244, [])  in
                   (uu____12237, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12262 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12262
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____12263 =
                     let uu____12270 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12270, [])  in
                   (uu____12263, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____12286 =
                     let uu____12293 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12293, [])  in
                   (uu____12286, [(t1, FStar_Parser_AST.Nothing)])
               | uu____12316 ->
                   let default_effect =
                     let uu____12318 = FStar_Options.ml_ish ()  in
                     if uu____12318
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____12321 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____12321
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____12323 =
                     let uu____12330 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12330, [])  in
                   (uu____12323, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____12353 = pre_process_comp_typ t  in
        match uu____12353 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____12402 =
                       let uu____12407 =
                         let uu____12408 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____12408
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____12407)
                        in
                     fail1 () uu____12402)
                else Obj.repr ());
             (let is_universe uu____12417 =
                match uu____12417 with
                | (uu____12422,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____12424 = FStar_Util.take is_universe args  in
              match uu____12424 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____12483  ->
                         match uu____12483 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____12490 =
                    let uu____12505 = FStar_List.hd args1  in
                    let uu____12514 = FStar_List.tl args1  in
                    (uu____12505, uu____12514)  in
                  (match uu____12490 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____12569 =
                         let is_decrease uu____12605 =
                           match uu____12605 with
                           | (t1,uu____12615) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____12625;
                                       FStar_Syntax_Syntax.vars = uu____12626;_},uu____12627::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____12658 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____12569 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____12772  ->
                                      match uu____12772 with
                                      | (t1,uu____12782) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____12791,(arg,uu____12793)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____12822 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____12835 -> false  in
                              (((is_empty () (Obj.magic decreases_clause)) &&
                                  (is_empty () (Obj.magic rest2)))
                                 && (is_empty () (Obj.magic cattributes)))
                                && (is_empty () (Obj.magic universes1))
                               in
                            let uu____12838 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____12838
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____12842 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____12842
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____12849 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____12849
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____12853 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____12853
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____12857 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____12857
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____12861 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____12861
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____12879 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____12879
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
                                                  let uu____12968 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____12968
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
                                            | uu____12983 -> pat  in
                                          let uu____12984 =
                                            let uu____12995 =
                                              let uu____13006 =
                                                let uu____13015 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____13015, aq)  in
                                              [uu____13006]  in
                                            ens :: uu____12995  in
                                          req :: uu____12984
                                      | uu____13056 -> rest2
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
        | uu____13078 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___130_13095 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___130_13095.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___130_13095.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___131_13129 = b  in
             {
               FStar_Parser_AST.b = (uu___131_13129.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___131_13129.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___131_13129.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____13188 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____13188)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____13201 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____13201 with
             | (env1,a1) ->
                 let a2 =
                   let uu___132_13211 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___132_13211.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___132_13211.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____13233 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____13247 =
                     let uu____13250 =
                       let uu____13251 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____13251]  in
                     no_annot_abs uu____13250 body2  in
                   FStar_All.pipe_left setpos uu____13247  in
                 let uu____13256 =
                   let uu____13257 =
                     let uu____13272 =
                       let uu____13273 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____13273
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____13274 =
                       let uu____13277 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____13277]  in
                     (uu____13272, uu____13274)  in
                   FStar_Syntax_Syntax.Tm_app uu____13257  in
                 FStar_All.pipe_left mk1 uu____13256)
        | uu____13282 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____13354 = q (rest, pats, body)  in
              let uu____13361 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____13354 uu____13361
                FStar_Parser_AST.Formula
               in
            let uu____13362 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____13362 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____13371 -> failwith "impossible"  in
      let uu____13374 =
        let uu____13375 = unparen f  in uu____13375.FStar_Parser_AST.tm  in
      match uu____13374 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____13382,uu____13383) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____13394,uu____13395) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13426 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____13426
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13462 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____13462
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____13505 -> desugar_term env f

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
      let uu____13510 =
        FStar_List.fold_left
          (fun uu____13546  ->
             fun b  ->
               match uu____13546 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___133_13598 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___133_13598.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___133_13598.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___133_13598.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____13615 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____13615 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___134_13635 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___134_13635.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___134_13635.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____13652 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____13510 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____13739 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____13739)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____13744 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____13744)
      | FStar_Parser_AST.TVariable x ->
          let uu____13748 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____13748)
      | FStar_Parser_AST.NoName t ->
          let uu____13756 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____13756)
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
               (fun uu___96_13789  ->
                  match uu___96_13789 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____13790 -> false))
           in
        let quals2 q =
          let uu____13801 =
            (let uu____13804 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____13804) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____13801
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____13818 = FStar_Ident.range_of_lid disc_name  in
                let uu____13819 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____13818;
                  FStar_Syntax_Syntax.sigquals = uu____13819;
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
            let uu____13850 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____13880  ->
                        match uu____13880 with
                        | (x,uu____13888) ->
                            let uu____13889 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____13889 with
                             | (field_name,uu____13897) ->
                                 let only_decl =
                                   ((let uu____13901 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____13901)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____13903 =
                                        let uu____13904 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____13904.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____13903)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____13918 =
                                       FStar_List.filter
                                         (fun uu___97_13922  ->
                                            match uu___97_13922 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____13923 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____13918
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___98_13936  ->
                                             match uu___98_13936 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____13937 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____13939 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____13939;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____13946 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____13946
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____13951 =
                                        let uu____13956 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____13956  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____13951;
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
                                      let uu____13960 =
                                        let uu____13961 =
                                          let uu____13968 =
                                            let uu____13971 =
                                              let uu____13972 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____13972
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____13971]  in
                                          ((false, [lb]), uu____13968)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____13961
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____13960;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____13850 FStar_List.flatten
  
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
            (lid,uu____14016,t,uu____14018,n1,uu____14020) when
            let uu____14025 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____14025 ->
            let uu____14026 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____14026 with
             | (formals,uu____14042) ->
                 (match formals with
                  | [] -> []
                  | uu____14065 ->
                      let filter_records uu___99_14077 =
                        match uu___99_14077 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____14080,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____14092 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____14094 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____14094 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____14104 = FStar_Util.first_N n1 formals  in
                      (match uu____14104 with
                       | (uu____14127,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____14153 -> []
  
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
                    let uu____14203 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____14203
                    then
                      let uu____14206 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____14206
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____14209 =
                      let uu____14214 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____14214  in
                    let uu____14215 =
                      let uu____14218 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____14218  in
                    let uu____14221 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____14209;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____14215;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____14221;
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
          let tycon_id uu___100_14268 =
            match uu___100_14268 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____14270,uu____14271) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____14281,uu____14282,uu____14283) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____14293,uu____14294,uu____14295) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____14325,uu____14326,uu____14327) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____14369) ->
                let uu____14370 =
                  let uu____14371 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14371  in
                FStar_Parser_AST.mk_term uu____14370 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____14373 =
                  let uu____14374 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14374  in
                FStar_Parser_AST.mk_term uu____14373 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____14376) ->
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
              | uu____14399 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____14405 =
                     let uu____14406 =
                       let uu____14413 = binder_to_term b  in
                       (out, uu____14413, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____14406  in
                   FStar_Parser_AST.mk_term uu____14405
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___101_14423 =
            match uu___101_14423 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____14479  ->
                       match uu____14479 with
                       | (x,t,uu____14490) ->
                           let uu____14495 =
                             let uu____14496 =
                               let uu____14501 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____14501, t)  in
                             FStar_Parser_AST.Annotated uu____14496  in
                           FStar_Parser_AST.mk_binder uu____14495
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____14503 =
                    let uu____14504 =
                      let uu____14505 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____14505  in
                    FStar_Parser_AST.mk_term uu____14504
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____14503 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____14509 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____14536  ->
                          match uu____14536 with
                          | (x,uu____14546,uu____14547) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____14509)
            | uu____14600 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___102_14631 =
            match uu___102_14631 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____14655 = typars_of_binders _env binders  in
                (match uu____14655 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____14701 =
                         let uu____14702 =
                           let uu____14703 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____14703  in
                         FStar_Parser_AST.mk_term uu____14702
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____14701 binders  in
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
            | uu____14716 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____14760 =
              FStar_List.fold_left
                (fun uu____14800  ->
                   fun uu____14801  ->
                     match (uu____14800, uu____14801) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____14892 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____14892 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____14760 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____15005 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____15005
                | uu____15006 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____15014 = desugar_abstract_tc quals env [] tc  in
              (match uu____15014 with
               | (uu____15027,uu____15028,se,uu____15030) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____15033,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____15050 =
                                 let uu____15051 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____15051  in
                               if uu____15050
                               then
                                 let uu____15052 =
                                   let uu____15057 =
                                     let uu____15058 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____15058
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____15057)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____15052
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
                           | uu____15065 ->
                               let uu____15066 =
                                 let uu____15069 =
                                   let uu____15070 =
                                     let uu____15083 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____15083)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____15070
                                    in
                                 FStar_Syntax_Syntax.mk uu____15069  in
                               uu____15066 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___135_15087 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___135_15087.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___135_15087.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___135_15087.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____15090 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____15093 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____15093
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____15108 = typars_of_binders env binders  in
              (match uu____15108 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15144 =
                           FStar_Util.for_some
                             (fun uu___103_15146  ->
                                match uu___103_15146 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____15147 -> false) quals
                            in
                         if uu____15144
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____15154 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___104_15158  ->
                               match uu___104_15158 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____15159 -> false))
                        in
                     if uu____15154
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____15168 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____15168
                     then
                       let uu____15171 =
                         let uu____15178 =
                           let uu____15179 = unparen t  in
                           uu____15179.FStar_Parser_AST.tm  in
                         match uu____15178 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____15200 =
                               match FStar_List.rev args with
                               | (last_arg,uu____15230)::args_rev ->
                                   let uu____15242 =
                                     let uu____15243 = unparen last_arg  in
                                     uu____15243.FStar_Parser_AST.tm  in
                                   (match uu____15242 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____15271 -> ([], args))
                               | uu____15280 -> ([], args)  in
                             (match uu____15200 with
                              | (cattributes,args1) ->
                                  let uu____15319 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____15319))
                         | uu____15330 -> (t, [])  in
                       match uu____15171 with
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
                                  (fun uu___105_15352  ->
                                     match uu___105_15352 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____15353 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____15364)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____15388 = tycon_record_as_variant trec  in
              (match uu____15388 with
               | (t,fs) ->
                   let uu____15405 =
                     let uu____15408 =
                       let uu____15409 =
                         let uu____15418 =
                           let uu____15421 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____15421  in
                         (uu____15418, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____15409  in
                     uu____15408 :: quals  in
                   desugar_tycon env d uu____15405 [t])
          | uu____15426::uu____15427 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____15588 = et  in
                match uu____15588 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____15813 ->
                         let trec = tc  in
                         let uu____15837 = tycon_record_as_variant trec  in
                         (match uu____15837 with
                          | (t,fs) ->
                              let uu____15896 =
                                let uu____15899 =
                                  let uu____15900 =
                                    let uu____15909 =
                                      let uu____15912 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____15912  in
                                    (uu____15909, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____15900
                                   in
                                uu____15899 :: quals1  in
                              collect_tcs uu____15896 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____15999 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____15999 with
                          | (env2,uu____16059,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____16208 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16208 with
                          | (env2,uu____16268,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____16393 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____16440 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____16440 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___107_16951  ->
                             match uu___107_16951 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____17018,uu____17019);
                                    FStar_Syntax_Syntax.sigrng = uu____17020;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____17021;
                                    FStar_Syntax_Syntax.sigmeta = uu____17022;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17023;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____17084 =
                                     typars_of_binders env1 binders  in
                                   match uu____17084 with
                                   | (env2,tpars1) ->
                                       let uu____17115 =
                                         push_tparams env2 tpars1  in
                                       (match uu____17115 with
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
                                 let uu____17148 =
                                   let uu____17169 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____17169)
                                    in
                                 [uu____17148]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____17237);
                                    FStar_Syntax_Syntax.sigrng = uu____17238;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____17240;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17241;_},constrs,tconstr,quals1)
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
                                 let uu____17337 = push_tparams env1 tpars
                                    in
                                 (match uu____17337 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____17414  ->
                                             match uu____17414 with
                                             | (x,uu____17428) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____17436 =
                                        let uu____17465 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____17579  ->
                                                  match uu____17579 with
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
                                                        let uu____17635 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____17635
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
                                                                uu___106_17646
                                                                 ->
                                                                match uu___106_17646
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____17658
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____17666 =
                                                        let uu____17687 =
                                                          let uu____17688 =
                                                            let uu____17689 =
                                                              let uu____17704
                                                                =
                                                                let uu____17707
                                                                  =
                                                                  let uu____17710
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____17710
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____17707
                                                                 in
                                                              (name, univs1,
                                                                uu____17704,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____17689
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____17688;
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
                                                          uu____17687)
                                                         in
                                                      (name, uu____17666)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____17465
                                         in
                                      (match uu____17436 with
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
                             | uu____17949 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18081  ->
                             match uu____18081 with
                             | (name_doc,uu____18109,uu____18110) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18190  ->
                             match uu____18190 with
                             | (uu____18211,uu____18212,se) -> se))
                      in
                   let uu____18242 =
                     let uu____18249 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____18249 rng
                      in
                   (match uu____18242 with
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
                               (fun uu____18315  ->
                                  match uu____18315 with
                                  | (uu____18338,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____18389,tps,k,uu____18392,constrs)
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
                                  | uu____18411 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____18428  ->
                                 match uu____18428 with
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
      let uu____18463 =
        FStar_List.fold_left
          (fun uu____18486  ->
             fun b  ->
               match uu____18486 with
               | (env1,binders1) ->
                   let uu____18506 = desugar_binder env1 b  in
                   (match uu____18506 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18523 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____18523 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____18540 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____18463 with
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
          let uu____18585 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___108_18590  ->
                    match uu___108_18590 with
                    | FStar_Syntax_Syntax.Reflectable uu____18591 -> true
                    | uu____18592 -> false))
             in
          if uu____18585
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____18595 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____18595
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
                  let uu____18699 = desugar_binders monad_env eff_binders  in
                  match uu____18699 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____18720 =
                          let uu____18721 =
                            let uu____18728 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____18728  in
                          FStar_List.length uu____18721  in
                        uu____18720 = (Prims.parse_int "1")  in
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
                            (uu____18770,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____18772,uu____18773,uu____18774),uu____18775)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____18808 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____18809 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____18821 = name_of_eff_decl decl  in
                             FStar_List.mem uu____18821 mandatory_members)
                          eff_decls
                         in
                      (match uu____18809 with
                       | (mandatory_members_decls,actions) ->
                           let uu____18838 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____18867  ->
                                     fun decl  ->
                                       match uu____18867 with
                                       | (env2,out) ->
                                           let uu____18887 =
                                             desugar_decl env2 decl  in
                                           (match uu____18887 with
                                            | (env3,ses) ->
                                                let uu____18900 =
                                                  let uu____18903 =
                                                    FStar_List.hd ses  in
                                                  uu____18903 :: out  in
                                                (env3, uu____18900)))
                                  (env1, []))
                              in
                           (match uu____18838 with
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
                                              (uu____18971,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____18974,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____18975,
                                                                  (def,uu____18977)::
                                                                  (cps_type,uu____18979)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____18980;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____18981;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____19033 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19033 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19053 =
                                                     let uu____19054 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19055 =
                                                       let uu____19056 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19056
                                                        in
                                                     let uu____19061 =
                                                       let uu____19062 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19062
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19054;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19055;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____19061
                                                     }  in
                                                   (uu____19053, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____19069,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____19072,defn),doc1)::[])
                                              when for_free ->
                                              let uu____19107 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19107 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19127 =
                                                     let uu____19128 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19129 =
                                                       let uu____19130 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19130
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19128;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19129;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____19127, doc1))
                                          | uu____19137 ->
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
                                    let uu____19167 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____19167
                                     in
                                  let uu____19168 =
                                    let uu____19169 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____19169
                                     in
                                  ([], uu____19168)  in
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
                                      let uu____19186 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____19186)  in
                                    let uu____19193 =
                                      let uu____19194 =
                                        let uu____19195 =
                                          let uu____19196 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19196
                                           in
                                        let uu____19205 = lookup1 "return"
                                           in
                                        let uu____19206 = lookup1 "bind"  in
                                        let uu____19207 =
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
                                            uu____19195;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____19205;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____19206;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____19207
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____19194
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____19193;
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
                                         (fun uu___109_19213  ->
                                            match uu___109_19213 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____19214 -> true
                                            | uu____19215 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____19225 =
                                       let uu____19226 =
                                         let uu____19227 =
                                           lookup1 "return_wp"  in
                                         let uu____19228 = lookup1 "bind_wp"
                                            in
                                         let uu____19229 =
                                           lookup1 "if_then_else"  in
                                         let uu____19230 = lookup1 "ite_wp"
                                            in
                                         let uu____19231 = lookup1 "stronger"
                                            in
                                         let uu____19232 = lookup1 "close_wp"
                                            in
                                         let uu____19233 = lookup1 "assert_p"
                                            in
                                         let uu____19234 = lookup1 "assume_p"
                                            in
                                         let uu____19235 = lookup1 "null_wp"
                                            in
                                         let uu____19236 = lookup1 "trivial"
                                            in
                                         let uu____19237 =
                                           if rr
                                           then
                                             let uu____19238 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____19238
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____19254 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____19256 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____19258 =
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
                                             uu____19227;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____19228;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____19229;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____19230;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____19231;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____19232;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____19233;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____19234;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____19235;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____19236;
                                           FStar_Syntax_Syntax.repr =
                                             uu____19237;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____19254;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____19256;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____19258
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____19226
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____19225;
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
                                          fun uu____19284  ->
                                            match uu____19284 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____19298 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____19298
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
                let uu____19322 = desugar_binders env1 eff_binders  in
                match uu____19322 with
                | (env2,binders) ->
                    let uu____19341 =
                      let uu____19360 = head_and_args defn  in
                      match uu____19360 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____19405 ->
                                let uu____19406 =
                                  let uu____19411 =
                                    let uu____19412 =
                                      let uu____19413 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____19413 " not found"
                                       in
                                    Prims.strcat "Effect " uu____19412  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____19411)
                                   in
                                FStar_Errors.raise_error uu____19406
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____19415 =
                            match FStar_List.rev args with
                            | (last_arg,uu____19445)::args_rev ->
                                let uu____19457 =
                                  let uu____19458 = unparen last_arg  in
                                  uu____19458.FStar_Parser_AST.tm  in
                                (match uu____19457 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____19486 -> ([], args))
                            | uu____19495 -> ([], args)  in
                          (match uu____19415 with
                           | (cattributes,args1) ->
                               let uu____19546 = desugar_args env2 args1  in
                               let uu____19555 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____19546, uu____19555))
                       in
                    (match uu____19341 with
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
                          (let uu____19611 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____19611 with
                           | (ed_binders,uu____19625,ed_binders_opening) ->
                               let sub1 uu____19636 =
                                 match uu____19636 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____19650 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____19650 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____19654 =
                                       let uu____19655 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____19655)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____19654
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____19660 =
                                   let uu____19661 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____19661
                                    in
                                 let uu____19672 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____19673 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____19674 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____19675 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____19676 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____19677 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____19678 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____19679 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____19680 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____19681 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____19682 =
                                   let uu____19683 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____19683
                                    in
                                 let uu____19694 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____19695 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____19696 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____19704 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____19705 =
                                          let uu____19706 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19706
                                           in
                                        let uu____19717 =
                                          let uu____19718 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19718
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____19704;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____19705;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____19717
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
                                     uu____19660;
                                   FStar_Syntax_Syntax.ret_wp = uu____19672;
                                   FStar_Syntax_Syntax.bind_wp = uu____19673;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____19674;
                                   FStar_Syntax_Syntax.ite_wp = uu____19675;
                                   FStar_Syntax_Syntax.stronger = uu____19676;
                                   FStar_Syntax_Syntax.close_wp = uu____19677;
                                   FStar_Syntax_Syntax.assert_p = uu____19678;
                                   FStar_Syntax_Syntax.assume_p = uu____19679;
                                   FStar_Syntax_Syntax.null_wp = uu____19680;
                                   FStar_Syntax_Syntax.trivial = uu____19681;
                                   FStar_Syntax_Syntax.repr = uu____19682;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____19694;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____19695;
                                   FStar_Syntax_Syntax.actions = uu____19696;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____19731 =
                                     let uu____19732 =
                                       let uu____19739 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____19739
                                        in
                                     FStar_List.length uu____19732  in
                                   uu____19731 = (Prims.parse_int "1")  in
                                 let uu____19768 =
                                   let uu____19771 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____19771 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____19768;
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
                                             let uu____19791 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____19791
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____19793 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____19793
                                 then
                                   let reflect_lid =
                                     let uu____19797 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____19797
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
    let uu____19809 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____19809 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____19860 ->
              let uu____19861 =
                let uu____19862 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____19862
                 in
              Prims.strcat "\n  " uu____19861
          | uu____19863 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____19876  ->
               match uu____19876 with
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
          let uu____19894 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____19894
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____19896 =
          let uu____19905 = FStar_Syntax_Syntax.as_arg arg  in [uu____19905]
           in
        FStar_Syntax_Util.mk_app fv uu____19896

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____19912 = desugar_decl_noattrs env d  in
      match uu____19912 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____19932 = mk_comment_attr d  in uu____19932 :: attrs1  in
          let uu____19937 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___136_19943 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___136_19943.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___136_19943.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___136_19943.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___136_19943.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____19937)

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
      | FStar_Parser_AST.Fsdoc uu____19969 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____19985 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____19985, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____20024  ->
                 match uu____20024 with | (x,uu____20032) -> x) tcs
             in
          let uu____20037 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____20037 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____20059;
                    FStar_Parser_AST.prange = uu____20060;_},uu____20061)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____20070;
                    FStar_Parser_AST.prange = uu____20071;_},uu____20072)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____20087;
                         FStar_Parser_AST.prange = uu____20088;_},uu____20089);
                    FStar_Parser_AST.prange = uu____20090;_},uu____20091)::[]
                   -> false
               | (p,uu____20119)::[] ->
                   let uu____20128 = is_app_pattern p  in
                   Prims.op_Negation uu____20128
               | uu____20129 -> false)
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
            let uu____20202 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____20202 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____20214 =
                     let uu____20215 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____20215.FStar_Syntax_Syntax.n  in
                   match uu____20214 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____20223) ->
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
                         | uu____20256::uu____20257 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____20260 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___110_20275  ->
                                     match uu___110_20275 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____20278;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20279;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20280;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20281;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20282;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20283;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20284;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20296;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20297;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20298;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20299;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20300;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20301;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____20315 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____20346  ->
                                   match uu____20346 with
                                   | (uu____20359,(uu____20360,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____20315
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____20384 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____20384
                         then
                           let uu____20393 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___137_20407 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___138_20409 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___138_20409.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___138_20409.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___137_20407.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___137_20407.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___137_20407.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___137_20407.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___137_20407.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___137_20407.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____20393)
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
                   | uu____20444 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____20450 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____20469 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____20450 with
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
                       let uu___139_20505 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___139_20505.FStar_Parser_AST.prange)
                       }
                   | uu____20512 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___140_20519 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___140_20519.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___140_20519.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___140_20519.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____20551 id1 =
                   match uu____20551 with
                   | (env1,ses) ->
                       let main =
                         let uu____20572 =
                           let uu____20573 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____20573  in
                         FStar_Parser_AST.mk_term uu____20572
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
                       let uu____20623 = desugar_decl env1 id_decl  in
                       (match uu____20623 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____20641 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____20641 FStar_Util.set_elements
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
            let uu____20672 = close_fun env t  in
            desugar_term env uu____20672  in
          let quals1 =
            let uu____20676 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____20676
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____20682 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____20682;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____20694 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____20694 with
           | (t,uu____20708) ->
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
            let uu____20742 =
              let uu____20749 = FStar_Syntax_Syntax.null_binder t  in
              [uu____20749]  in
            let uu____20750 =
              let uu____20753 =
                let uu____20754 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____20754  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____20753
               in
            FStar_Syntax_Util.arrow uu____20742 uu____20750  in
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
            let uu____20817 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____20817 with
            | FStar_Pervasives_Native.None  ->
                let uu____20820 =
                  let uu____20825 =
                    let uu____20826 =
                      let uu____20827 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____20827 " not found"  in
                    Prims.strcat "Effect name " uu____20826  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____20825)  in
                FStar_Errors.raise_error uu____20820
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____20831 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____20873 =
                  let uu____20882 =
                    let uu____20889 = desugar_term env t  in
                    ([], uu____20889)  in
                  FStar_Pervasives_Native.Some uu____20882  in
                (uu____20873, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____20922 =
                  let uu____20931 =
                    let uu____20938 = desugar_term env wp  in
                    ([], uu____20938)  in
                  FStar_Pervasives_Native.Some uu____20931  in
                let uu____20947 =
                  let uu____20956 =
                    let uu____20963 = desugar_term env t  in
                    ([], uu____20963)  in
                  FStar_Pervasives_Native.Some uu____20956  in
                (uu____20922, uu____20947)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____20989 =
                  let uu____20998 =
                    let uu____21005 = desugar_term env t  in
                    ([], uu____21005)  in
                  FStar_Pervasives_Native.Some uu____20998  in
                (FStar_Pervasives_Native.None, uu____20989)
             in
          (match uu____20831 with
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
            let uu____21085 =
              let uu____21086 =
                let uu____21093 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____21093, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____21086  in
            {
              FStar_Syntax_Syntax.sigel = uu____21085;
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
      let uu____21117 =
        FStar_List.fold_left
          (fun uu____21137  ->
             fun d  ->
               match uu____21137 with
               | (env1,sigelts) ->
                   let uu____21157 = desugar_decl env1 d  in
                   (match uu____21157 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____21117 with
      | (env1,sigelts) ->
          let rec forward acc uu___112_21198 =
            match uu___112_21198 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____21212,FStar_Syntax_Syntax.Sig_let uu____21213) ->
                     let uu____21226 =
                       let uu____21229 =
                         let uu___141_21230 = se2  in
                         let uu____21231 =
                           let uu____21234 =
                             FStar_List.filter
                               (fun uu___111_21248  ->
                                  match uu___111_21248 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____21252;
                                           FStar_Syntax_Syntax.vars =
                                             uu____21253;_},uu____21254);
                                      FStar_Syntax_Syntax.pos = uu____21255;
                                      FStar_Syntax_Syntax.vars = uu____21256;_}
                                      when
                                      let uu____21279 =
                                        let uu____21280 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____21280
                                         in
                                      uu____21279 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____21281 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____21234
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___141_21230.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___141_21230.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___141_21230.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___141_21230.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____21231
                         }  in
                       uu____21229 :: se1 :: acc  in
                     forward uu____21226 sigelts1
                 | uu____21286 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____21294 = forward [] sigelts  in (env1, uu____21294)
  
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
      let uu____21328 =
        let uu____21333 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____21350  ->
               match uu____21350 with
               | ({ FStar_Syntax_Syntax.ppname = uu____21359;
                    FStar_Syntax_Syntax.index = uu____21360;
                    FStar_Syntax_Syntax.sort = t;_},uu____21362)
                   ->
                   let uu____21365 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____21365) uu____21333
         in
      FStar_All.pipe_right bs uu____21328  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____21373 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____21390 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____21418 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____21439,uu____21440,bs,t,uu____21443,uu____21444)
                            ->
                            let uu____21453 = bs_univnames bs  in
                            let uu____21456 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____21453 uu____21456
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____21459,uu____21460,t,uu____21462,uu____21463,uu____21464)
                            -> FStar_Syntax_Free.univnames t
                        | uu____21469 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____21418 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___142_21479 = s  in
        let uu____21480 =
          let uu____21481 =
            let uu____21490 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____21508,bs,t,lids1,lids2) ->
                          let uu___143_21521 = se  in
                          let uu____21522 =
                            let uu____21523 =
                              let uu____21540 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____21541 =
                                let uu____21542 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____21542 t  in
                              (lid, uvs, uu____21540, uu____21541, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____21523
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____21522;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___143_21521.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___143_21521.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___143_21521.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___143_21521.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____21556,t,tlid,n1,lids1) ->
                          let uu___144_21565 = se  in
                          let uu____21566 =
                            let uu____21567 =
                              let uu____21582 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____21582, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____21567  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____21566;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___144_21565.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___144_21565.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___144_21565.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___144_21565.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____21587 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____21490, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____21481  in
        {
          FStar_Syntax_Syntax.sigel = uu____21480;
          FStar_Syntax_Syntax.sigrng =
            (uu___142_21479.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___142_21479.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___142_21479.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___142_21479.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____21593,t) ->
        let uvs =
          let uu____21598 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____21598 FStar_Util.set_elements  in
        let uu___145_21605 = s  in
        let uu____21606 =
          let uu____21607 =
            let uu____21614 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____21614)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____21607  in
        {
          FStar_Syntax_Syntax.sigel = uu____21606;
          FStar_Syntax_Syntax.sigrng =
            (uu___145_21605.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___145_21605.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___145_21605.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___145_21605.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____21642 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____21645 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____21652) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____21681,(FStar_Util.Inl t,uu____21683),uu____21684)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____21731,(FStar_Util.Inr c,uu____21733),uu____21734)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____21781 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____21782,(FStar_Util.Inl t,uu____21784),uu____21785) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____21832,(FStar_Util.Inr c,uu____21834),uu____21835) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____21882 -> empty_set  in
          FStar_Util.set_union uu____21642 uu____21645  in
        let all_lb_univs =
          let uu____21886 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____21902 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____21902) empty_set)
             in
          FStar_All.pipe_right uu____21886 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___146_21912 = s  in
        let uu____21913 =
          let uu____21914 =
            let uu____21921 =
              let uu____21928 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___147_21940 = lb  in
                        let uu____21941 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____21944 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___147_21940.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____21941;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___147_21940.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____21944;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___147_21940.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___147_21940.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____21928)  in
            (uu____21921, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____21914  in
        {
          FStar_Syntax_Syntax.sigel = uu____21913;
          FStar_Syntax_Syntax.sigrng =
            (uu___146_21912.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___146_21912.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___146_21912.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___146_21912.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____21958,fml) ->
        let uvs =
          let uu____21963 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____21963 FStar_Util.set_elements  in
        let uu___148_21970 = s  in
        let uu____21971 =
          let uu____21972 =
            let uu____21979 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____21979)  in
          FStar_Syntax_Syntax.Sig_assume uu____21972  in
        {
          FStar_Syntax_Syntax.sigel = uu____21971;
          FStar_Syntax_Syntax.sigrng =
            (uu___148_21970.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___148_21970.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___148_21970.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___148_21970.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____21983,bs,c,flags1) ->
        let uvs =
          let uu____21994 =
            let uu____21997 = bs_univnames bs  in
            let uu____22000 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____21997 uu____22000  in
          FStar_All.pipe_right uu____21994 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___149_22010 = s  in
        let uu____22011 =
          let uu____22012 =
            let uu____22025 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____22026 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____22025, uu____22026, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____22012  in
        {
          FStar_Syntax_Syntax.sigel = uu____22011;
          FStar_Syntax_Syntax.sigrng =
            (uu___149_22010.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___149_22010.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___149_22010.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___149_22010.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____22031 -> s
  
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
          | (FStar_Pervasives_Native.None ,uu____22060) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____22064;
               FStar_Syntax_Syntax.exports = uu____22065;
               FStar_Syntax_Syntax.is_interface = uu____22066;_},FStar_Parser_AST.Module
             (current_lid,uu____22068)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____22076) ->
              let uu____22079 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____22079
           in
        let uu____22084 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____22120 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____22120, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____22137 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____22137, mname, decls, false)
           in
        match uu____22084 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____22167 = desugar_decls env2 decls  in
            (match uu____22167 with
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
          let uu____22228 =
            (FStar_Options.interactive ()) &&
              (let uu____22230 =
                 let uu____22231 =
                   let uu____22232 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____22232  in
                 FStar_Util.get_file_extension uu____22231  in
               FStar_List.mem uu____22230 ["fsti"; "fsi"])
             in
          if uu____22228 then as_interface m else m  in
        let uu____22236 = desugar_modul_common curmod env m1  in
        match uu____22236 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____22251 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____22267 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____22267 with
      | (env1,modul,pop_when_done) ->
          let uu____22281 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____22281 with
           | (env2,modul1) ->
               ((let uu____22293 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____22293
                 then
                   let uu____22294 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____22294
                 else ());
                (let uu____22296 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____22296, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____22310 = desugar_modul env modul  in
      match uu____22310 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____22337 = desugar_decls env decls  in
      match uu____22337 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____22375 = desugar_partial_modul modul env a_modul  in
        match uu____22375 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____22449 ->
                  let t =
                    let uu____22457 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____22457  in
                  let uu____22466 =
                    let uu____22467 = FStar_Syntax_Subst.compress t  in
                    uu____22467.FStar_Syntax_Syntax.n  in
                  (match uu____22466 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____22477,uu____22478)
                       -> bs1
                   | uu____22499 -> failwith "Impossible")
               in
            let uu____22506 =
              let uu____22513 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____22513
                FStar_Syntax_Syntax.t_unit
               in
            match uu____22506 with
            | (binders,uu____22515,binders_opening) ->
                let erase_term t =
                  let uu____22521 =
                    let uu____22522 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____22522  in
                  FStar_Syntax_Subst.close binders uu____22521  in
                let erase_tscheme uu____22538 =
                  match uu____22538 with
                  | (us,t) ->
                      let t1 =
                        let uu____22558 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____22558 t  in
                      let uu____22561 =
                        let uu____22562 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____22562  in
                      ([], uu____22561)
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
                    | uu____22591 ->
                        let bs =
                          let uu____22599 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____22599  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____22629 =
                          let uu____22630 =
                            let uu____22633 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____22633  in
                          uu____22630.FStar_Syntax_Syntax.n  in
                        (match uu____22629 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____22641,uu____22642) -> bs1
                         | uu____22663 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____22674 =
                      let uu____22675 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____22675  in
                    FStar_Syntax_Subst.close binders uu____22674  in
                  let uu___150_22676 = action  in
                  let uu____22677 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____22678 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___150_22676.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___150_22676.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____22677;
                    FStar_Syntax_Syntax.action_typ = uu____22678
                  }  in
                let uu___151_22679 = ed  in
                let uu____22680 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____22681 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____22682 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____22683 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____22684 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____22685 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____22686 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____22687 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____22688 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____22689 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____22690 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____22691 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____22692 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____22693 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____22694 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____22695 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___151_22679.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___151_22679.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____22680;
                  FStar_Syntax_Syntax.signature = uu____22681;
                  FStar_Syntax_Syntax.ret_wp = uu____22682;
                  FStar_Syntax_Syntax.bind_wp = uu____22683;
                  FStar_Syntax_Syntax.if_then_else = uu____22684;
                  FStar_Syntax_Syntax.ite_wp = uu____22685;
                  FStar_Syntax_Syntax.stronger = uu____22686;
                  FStar_Syntax_Syntax.close_wp = uu____22687;
                  FStar_Syntax_Syntax.assert_p = uu____22688;
                  FStar_Syntax_Syntax.assume_p = uu____22689;
                  FStar_Syntax_Syntax.null_wp = uu____22690;
                  FStar_Syntax_Syntax.trivial = uu____22691;
                  FStar_Syntax_Syntax.repr = uu____22692;
                  FStar_Syntax_Syntax.return_repr = uu____22693;
                  FStar_Syntax_Syntax.bind_repr = uu____22694;
                  FStar_Syntax_Syntax.actions = uu____22695;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___151_22679.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___152_22707 = se  in
                  let uu____22708 =
                    let uu____22709 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____22709  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____22708;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___152_22707.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___152_22707.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___152_22707.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___152_22707.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___153_22713 = se  in
                  let uu____22714 =
                    let uu____22715 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22715
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____22714;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___153_22713.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___153_22713.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___153_22713.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___153_22713.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____22717 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____22718 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____22718 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____22730 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____22730
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____22732 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____22732)
  