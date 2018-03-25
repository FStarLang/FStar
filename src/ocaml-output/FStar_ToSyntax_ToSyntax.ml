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
      | FStar_Parser_AST.Seq uu____841 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____888 =
        let uu____889 = unparen t1  in uu____889.FStar_Parser_AST.tm  in
      match uu____888 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____931 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____951 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____951  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____969 =
                     let uu____970 =
                       let uu____975 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____975)  in
                     FStar_Parser_AST.TAnnotated uu____970  in
                   FStar_Parser_AST.mk_binder uu____969 x.FStar_Ident.idRange
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
        let uu____988 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____988  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1006 =
                     let uu____1007 =
                       let uu____1012 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1012)  in
                     FStar_Parser_AST.TAnnotated uu____1007  in
                   FStar_Parser_AST.mk_binder uu____1006
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1014 =
             let uu____1015 = unparen t  in uu____1015.FStar_Parser_AST.tm
              in
           match uu____1014 with
           | FStar_Parser_AST.Product uu____1016 -> t
           | uu____1023 ->
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
      | uu____1055 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1061,uu____1062) -> true
    | FStar_Parser_AST.PatVar (uu____1067,uu____1068) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1074) -> is_var_pattern p1
    | uu____1087 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1092) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1105;
           FStar_Parser_AST.prange = uu____1106;_},uu____1107)
        -> true
    | uu____1118 -> false
  
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
    | uu____1130 -> p
  
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
            let uu____1194 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1194 with
             | (name,args,uu____1237) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1287);
               FStar_Parser_AST.prange = uu____1288;_},args)
            when is_top_level1 ->
            let uu____1298 =
              let uu____1303 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1303  in
            (uu____1298, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1325);
               FStar_Parser_AST.prange = uu____1326;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1356 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1400 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1401,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1404 -> acc
      | FStar_Parser_AST.PatTvar uu____1405 -> acc
      | FStar_Parser_AST.PatOp uu____1412 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1420) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1429) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1444 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1444
      | FStar_Parser_AST.PatAscribed (pat,uu____1452) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1508 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1542 -> false
  
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
  fun uu___88_1586  ->
    match uu___88_1586 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1593 -> failwith "Impossible"
  
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
      fun uu___89_1618  ->
        match uu___89_1618 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1634 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1634, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1639 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1639 with
             | (env1,a1) ->
                 (((let uu___113_1659 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___113_1659.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___113_1659.FStar_Syntax_Syntax.index);
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
  fun uu____1686  ->
    match uu____1686 with
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
      let uu____1754 =
        let uu____1769 =
          let uu____1770 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1770  in
        let uu____1771 =
          let uu____1780 =
            let uu____1787 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1787)  in
          [uu____1780]  in
        (uu____1769, uu____1771)  in
      FStar_Syntax_Syntax.Tm_app uu____1754  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1820 =
        let uu____1835 =
          let uu____1836 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1836  in
        let uu____1837 =
          let uu____1846 =
            let uu____1853 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1853)  in
          [uu____1846]  in
        (uu____1835, uu____1837)  in
      FStar_Syntax_Syntax.Tm_app uu____1820  in
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
          let uu____1896 =
            let uu____1911 =
              let uu____1912 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____1912  in
            let uu____1913 =
              let uu____1922 =
                let uu____1929 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____1929)  in
              let uu____1932 =
                let uu____1941 =
                  let uu____1948 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____1948)  in
                [uu____1941]  in
              uu____1922 :: uu____1932  in
            (uu____1911, uu____1913)  in
          FStar_Syntax_Syntax.Tm_app uu____1896  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___90_1979  ->
    match uu___90_1979 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1980 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1988 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1988)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2003 =
      let uu____2004 = unparen t  in uu____2004.FStar_Parser_AST.tm  in
    match uu____2003 with
    | FStar_Parser_AST.Wild  ->
        let uu____2009 =
          let uu____2010 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2010  in
        FStar_Util.Inr uu____2009
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2021)) ->
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
        ((let uu____2043 = Obj.magic ()  in ());
         (let u1 = desugar_maybe_non_constant_universe t1  in
          let u2 = desugar_maybe_non_constant_universe t2  in
          match (u1, u2) with
          | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
          | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
              let uu____2086 = sum_to_universe u n1  in
              FStar_Util.Inr uu____2086
          | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
              let uu____2097 = sum_to_universe u n1  in
              FStar_Util.Inr uu____2097
          | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
              let uu____2108 =
                let uu____2113 =
                  let uu____2114 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat
                    "This universe might contain a sum of two universe variables "
                    uu____2114
                   in
                (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                  uu____2113)
                 in
              FStar_Errors.raise_error uu____2108 t.FStar_Parser_AST.range))
    | FStar_Parser_AST.App uu____2119 ->
        let rec aux t1 univargs =
          let uu____2149 =
            let uu____2150 = unparen t1  in uu____2150.FStar_Parser_AST.tm
             in
          match uu____2149 with
          | FStar_Parser_AST.App (t2,targ,uu____2157) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              ((let uu____2169 = Obj.magic ()  in ());
               if
                 FStar_List.existsb
                   (fun uu___91_2180  ->
                      match uu___91_2180 with
                      | FStar_Util.Inr uu____2185 -> true
                      | uu____2186 -> false) univargs
               then
                 (let uu____2191 =
                    let uu____2192 =
                      FStar_List.map
                        (fun uu___92_2201  ->
                           match uu___92_2201 with
                           | FStar_Util.Inl n1 -> int_to_universe n1
                           | FStar_Util.Inr u -> u) univargs
                       in
                    FStar_Syntax_Syntax.U_max uu____2192  in
                  FStar_Util.Inr uu____2191)
               else
                 (let nargs =
                    FStar_List.map
                      (fun uu___93_2218  ->
                         match uu___93_2218 with
                         | FStar_Util.Inl n1 -> n1
                         | FStar_Util.Inr uu____2224 -> failwith "impossible")
                      univargs
                     in
                  let uu____2225 =
                    FStar_List.fold_left
                      (fun m  -> fun n1  -> if m > n1 then m else n1)
                      (Prims.parse_int "0") nargs
                     in
                  FStar_Util.Inl uu____2225))
          | uu____2231 ->
              let uu____2232 =
                let uu____2237 =
                  let uu____2238 =
                    let uu____2239 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2239 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2238  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2237)  in
              FStar_Errors.raise_error uu____2232 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2248 ->
        let uu____2249 =
          let uu____2254 =
            let uu____2255 =
              let uu____2256 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2256 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2255  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2254)  in
        FStar_Errors.raise_error uu____2249 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____2285 ->
        let uu____2308 =
          let uu____2313 =
            let uu____2314 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____2314
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____2313)  in
        FStar_Errors.raise_error uu____2308 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____2320 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2320) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2345 = FStar_List.hd fields  in
        match uu____2345 with
        | (f,uu____2355) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2365 =
                match uu____2365 with
                | (f',uu____2371) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2373 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____2373
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
              (let uu____2377 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2377);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2626 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2633 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2634 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2636,pats1) ->
                let aux out uu____2670 =
                  match uu____2670 with
                  | (p2,uu____2682) ->
                      let intersection =
                        let uu____2690 = pat_vars p2  in
                        FStar_Util.set_intersect uu____2690 out  in
                      let uu____2693 = FStar_Util.set_is_empty intersection
                         in
                      if uu____2693
                      then
                        let uu____2696 = pat_vars p2  in
                        FStar_Util.set_union out uu____2696
                      else
                        (let duplicate_bv =
                           let uu____2701 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____2701  in
                         let uu____2704 =
                           let uu____2709 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____2709)
                            in
                         FStar_Errors.raise_error uu____2704 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____2729 = pat_vars p1  in
              FStar_All.pipe_right uu____2729 FStar_Pervasives.ignore
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____2749 =
                  let uu____2750 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____2750  in
                if uu____2749
                then ()
                else
                  (let nonlinear_vars =
                     let uu____2757 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____2757  in
                   let first_nonlinear_var =
                     let uu____2761 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____2761  in
                   let uu____2764 =
                     let uu____2769 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____2769)  in
                   FStar_Errors.raise_error uu____2764 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2773) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2774) -> ()
         | (true ,uu____2781) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_Syntax_DsEnv.push_bv_mutable
           else FStar_Syntax_DsEnv.push_bv  in
         let resolvex l e x =
           let uu____2816 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2816 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2830 ->
               let uu____2833 = push_bv_maybe_mut e x  in
               (match uu____2833 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2920 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2936 =
                 let uu____2937 =
                   let uu____2938 =
                     let uu____2945 =
                       let uu____2946 =
                         let uu____2951 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2951, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2946  in
                     (uu____2945, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2938  in
                 {
                   FStar_Parser_AST.pat = uu____2937;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2936
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____2968 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____2969 = aux loc env1 p2  in
                 match uu____2969 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___114_3023 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___115_3028 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___115_3028.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___115_3028.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___114_3023.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___116_3030 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___117_3035 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___117_3035.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___117_3035.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___116_3030.FStar_Syntax_Syntax.p)
                           }
                       | uu____3036 when top -> p4
                       | uu____3037 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____3040 =
                       match binder with
                       | LetBinder uu____3053 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____3073 = close_fun env1 t  in
                             desugar_term env1 uu____3073  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____3075 -> true)
                            then
                              (let uu____3076 =
                                 let uu____3081 =
                                   let uu____3082 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____3083 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____3084 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3082 uu____3083 uu____3084
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3081)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3076)
                            else ();
                            (let uu____3086 = annot_pat_var p3 t1  in
                             (uu____3086,
                               (LocalBinder
                                  ((let uu___118_3092 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___118_3092.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___118_3092.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____3040 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3114 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3114, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3125 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3125, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3146 = resolvex loc env1 x  in
               (match uu____3146 with
                | (loc1,env2,xbv) ->
                    let uu____3168 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3168, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3189 = resolvex loc env1 x  in
               (match uu____3189 with
                | (loc1,env2,xbv) ->
                    let uu____3211 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3211, imp))
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
               let uu____3223 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3223, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3247;_},args)
               ->
               let uu____3253 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3294  ->
                        match uu____3294 with
                        | (loc1,env2,args1) ->
                            let uu____3342 = aux loc1 env2 arg  in
                            (match uu____3342 with
                             | (loc2,env3,uu____3371,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____3253 with
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
                    let uu____3441 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3441, false))
           | FStar_Parser_AST.PatApp uu____3458 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3480 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3513  ->
                        match uu____3513 with
                        | (loc1,env2,pats1) ->
                            let uu____3545 = aux loc1 env2 pat  in
                            (match uu____3545 with
                             | (loc2,env3,uu____3570,pat1,uu____3572) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3480 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3615 =
                        let uu____3618 =
                          let uu____3623 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3623  in
                        let uu____3624 =
                          let uu____3625 =
                            let uu____3638 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3638, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3625  in
                        FStar_All.pipe_left uu____3618 uu____3624  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3670 =
                               let uu____3671 =
                                 let uu____3684 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3684, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3671  in
                             FStar_All.pipe_left (pos_r r) uu____3670) pats1
                        uu____3615
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
               let uu____3728 =
                 FStar_List.fold_left
                   (fun uu____3768  ->
                      fun p2  ->
                        match uu____3768 with
                        | (loc1,env2,pats) ->
                            let uu____3817 = aux loc1 env2 p2  in
                            (match uu____3817 with
                             | (loc2,env3,uu____3846,pat,uu____3848) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3728 with
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
                    let uu____3943 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____3943 with
                     | (constr,uu____3965) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3968 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3970 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3970, false)))
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
                      (fun uu____4041  ->
                         match uu____4041 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4071  ->
                         match uu____4071 with
                         | (f,uu____4077) ->
                             let uu____4078 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4104  ->
                                       match uu____4104 with
                                       | (g,uu____4110) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____4078 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4115,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____4122 =
                   let uu____4123 =
                     let uu____4130 =
                       let uu____4131 =
                         let uu____4132 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____4132  in
                       FStar_Parser_AST.mk_pattern uu____4131
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____4130, args)  in
                   FStar_Parser_AST.PatApp uu____4123  in
                 FStar_Parser_AST.mk_pattern uu____4122
                   p1.FStar_Parser_AST.prange
                  in
               let uu____4135 = aux loc env1 app  in
               (match uu____4135 with
                | (env2,e,b,p2,uu____4164) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4192 =
                            let uu____4193 =
                              let uu____4206 =
                                let uu___119_4207 = fv  in
                                let uu____4208 =
                                  let uu____4211 =
                                    let uu____4212 =
                                      let uu____4219 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4219)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4212
                                     in
                                  FStar_Pervasives_Native.Some uu____4211  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___119_4207.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___119_4207.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4208
                                }  in
                              (uu____4206, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____4193  in
                          FStar_All.pipe_left pos uu____4192
                      | uu____4246 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4296 = aux' true loc env1 p2  in
               (match uu____4296 with
                | (loc1,env2,var,p3,uu____4323) ->
                    let uu____4328 =
                      FStar_List.fold_left
                        (fun uu____4360  ->
                           fun p4  ->
                             match uu____4360 with
                             | (loc2,env3,ps1) ->
                                 let uu____4393 = aux' true loc2 env3 p4  in
                                 (match uu____4393 with
                                  | (loc3,env4,uu____4418,p5,uu____4420) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____4328 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4471 ->
               let uu____4472 = aux' true loc env1 p1  in
               (match uu____4472 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4512 = aux_maybe_or env p  in
         match uu____4512 with
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
            let uu____4571 =
              let uu____4572 =
                let uu____4583 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4583,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4572  in
            (env, uu____4571, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4611 =
                  let uu____4612 =
                    let uu____4617 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4617, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4612  in
                mklet uu____4611
            | FStar_Parser_AST.PatVar (x,uu____4619) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4625);
                   FStar_Parser_AST.prange = uu____4626;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4646 =
                  let uu____4647 =
                    let uu____4658 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____4659 =
                      let uu____4666 = desugar_term env t  in
                      (uu____4666, tacopt1)  in
                    (uu____4658, uu____4659)  in
                  LetBinder uu____4647  in
                (env, uu____4646, [])
            | uu____4677 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4687 = desugar_data_pat env p is_mut  in
             match uu____4687 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4716;
                       FStar_Syntax_Syntax.p = uu____4717;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4722;
                       FStar_Syntax_Syntax.p = uu____4723;_}::[] -> []
                   | uu____4728 -> p1  in
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
  fun uu____4735  ->
    fun env  ->
      fun pat  ->
        let uu____4738 = desugar_data_pat env pat false  in
        match uu____4738 with | (env1,uu____4754,pat1) -> (env1, pat1)

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
      let uu____4773 = desugar_term_aq env e  in
      match uu____4773 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____4790 = desugar_typ_aq env e  in
      match uu____4790 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____4800  ->
        fun range  ->
          match uu____4800 with
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
              ((let uu____4810 =
                  let uu____4811 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4811  in
                if uu____4810
                then
                  let uu____4812 =
                    let uu____4817 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4817)  in
                  FStar_Errors.log_issue range uu____4812
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
                  let uu____4822 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____4822 range  in
                let lid1 =
                  let uu____4826 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____4826 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4836) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____4845 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____4845 range  in
                           let private_fv =
                             let uu____4847 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4847 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___120_4848 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___120_4848.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___120_4848.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4849 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4856 =
                        let uu____4861 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4861)
                         in
                      FStar_Errors.raise_error uu____4856 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4877 =
                  let uu____4880 =
                    let uu____4881 =
                      let uu____4896 =
                        let uu____4905 =
                          let uu____4912 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4912)  in
                        [uu____4905]  in
                      (lid1, uu____4896)  in
                    FStar_Syntax_Syntax.Tm_app uu____4881  in
                  FStar_Syntax_Syntax.mk uu____4880  in
                uu____4877 FStar_Pervasives_Native.None range))

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
            let uu____4951 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4951 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____4998;
                              FStar_Syntax_Syntax.vars = uu____4999;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5022 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5022 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5030 =
                                 let uu____5031 =
                                   let uu____5034 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____5034  in
                                 uu____5031.FStar_Syntax_Syntax.n  in
                               match uu____5030 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____5050))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5051 -> msg
                             else msg  in
                           let uu____5053 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5053
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5056 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5056 " is deprecated"  in
                           let uu____5057 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5057
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5058 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____5063 =
                      let uu____5064 =
                        let uu____5071 = mk_ref_read tm1  in
                        (uu____5071,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____5064  in
                    FStar_All.pipe_left mk1 uu____5063
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____5087 =
          let uu____5088 = unparen t  in uu____5088.FStar_Parser_AST.tm  in
        match uu____5087 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5089; FStar_Ident.ident = uu____5090;
              FStar_Ident.nsstr = uu____5091; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5094 ->
            let uu____5095 =
              let uu____5100 =
                let uu____5101 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5101  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5100)  in
            FStar_Errors.raise_error uu____5095 t.FStar_Parser_AST.range
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
          let uu___121_5190 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___121_5190.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___121_5190.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5193 =
          let uu____5194 = unparen top  in uu____5194.FStar_Parser_AST.tm  in
        match uu____5193 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5211 ->
            let uu____5218 = desugar_formula env top  in (uu____5218, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____5235 = desugar_formula env t  in (uu____5235, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____5252 = desugar_formula env t  in (uu____5252, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____5286 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____5286, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5298 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____5298, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____5320 =
                let uu____5321 =
                  let uu____5328 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____5328, args)  in
                FStar_Parser_AST.Op uu____5321  in
              FStar_Parser_AST.mk_term uu____5320 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____5331 =
              let uu____5332 =
                let uu____5333 =
                  let uu____5340 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____5340, [e])  in
                FStar_Parser_AST.Op uu____5333  in
              FStar_Parser_AST.mk_term uu____5332 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____5331
        | FStar_Parser_AST.Op (op_star,uu____5344::uu____5345::[]) when
            (let uu____5350 = FStar_Ident.text_of_id op_star  in
             uu____5350 = "*") &&
              (let uu____5352 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5352 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5365;_},t1::t2::[])
                  ->
                  let uu____5370 = flatten1 t1  in
                  FStar_List.append uu____5370 [t2]
              | uu____5373 -> [t]  in
            let uu____5374 =
              let uu____5383 =
                let uu____5390 =
                  let uu____5393 = unparen top  in flatten1 uu____5393  in
                FStar_All.pipe_right uu____5390
                  (FStar_List.map
                     (fun t  ->
                        let uu____5412 = desugar_typ_aq env t  in
                        match uu____5412 with
                        | (t',aq) ->
                            let uu____5423 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5423, aq)))
                 in
              FStar_All.pipe_right uu____5383 FStar_List.unzip  in
            (match uu____5374 with
             | (targs,aqs) ->
                 let uu____5452 =
                   let uu____5457 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5457
                    in
                 (match uu____5452 with
                  | (tup,uu____5467) ->
                      let uu____5468 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5468, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5486 =
              let uu____5489 =
                let uu____5492 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5492  in
              FStar_All.pipe_left setpos uu____5489  in
            (uu____5486, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5518 =
              let uu____5523 =
                let uu____5524 =
                  let uu____5525 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____5525 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____5524  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5523)  in
            FStar_Errors.raise_error uu____5518 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5536 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5536 with
             | FStar_Pervasives_Native.None  ->
                 let uu____5543 =
                   let uu____5548 =
                     let uu____5549 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5549
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5548)
                    in
                 FStar_Errors.raise_error uu____5543
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5559 =
                     let uu____5574 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____5616 = desugar_term_aq env t  in
                               match uu____5616 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____5574 FStar_List.unzip  in
                   (match uu____5559 with
                    | (args1,aqs) ->
                        let uu____5699 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____5699, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____5735)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____5750 =
              let uu___122_5751 = top  in
              let uu____5752 =
                let uu____5753 =
                  let uu____5760 =
                    let uu___123_5761 = top  in
                    let uu____5762 =
                      let uu____5763 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____5763  in
                    {
                      FStar_Parser_AST.tm = uu____5762;
                      FStar_Parser_AST.range =
                        (uu___123_5761.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___123_5761.FStar_Parser_AST.level)
                    }  in
                  (uu____5760, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____5753  in
              {
                FStar_Parser_AST.tm = uu____5752;
                FStar_Parser_AST.range =
                  (uu___122_5751.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___122_5751.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____5750
        | FStar_Parser_AST.Construct (n1,(a,uu____5766)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____5782 =
                let uu___124_5783 = top  in
                let uu____5784 =
                  let uu____5785 =
                    let uu____5792 =
                      let uu___125_5793 = top  in
                      let uu____5794 =
                        let uu____5795 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____5795  in
                      {
                        FStar_Parser_AST.tm = uu____5794;
                        FStar_Parser_AST.range =
                          (uu___125_5793.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___125_5793.FStar_Parser_AST.level)
                      }  in
                    (uu____5792, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____5785  in
                {
                  FStar_Parser_AST.tm = uu____5784;
                  FStar_Parser_AST.range =
                    (uu___124_5783.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___124_5783.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____5782))
        | FStar_Parser_AST.Construct (n1,(a,uu____5798)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____5813 =
              let uu___126_5814 = top  in
              let uu____5815 =
                let uu____5816 =
                  let uu____5823 =
                    let uu___127_5824 = top  in
                    let uu____5825 =
                      let uu____5826 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____5826  in
                    {
                      FStar_Parser_AST.tm = uu____5825;
                      FStar_Parser_AST.range =
                        (uu___127_5824.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___127_5824.FStar_Parser_AST.level)
                    }  in
                  (uu____5823, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____5816  in
              {
                FStar_Parser_AST.tm = uu____5815;
                FStar_Parser_AST.range =
                  (uu___126_5814.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___126_5814.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____5813
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5827; FStar_Ident.ident = uu____5828;
              FStar_Ident.nsstr = uu____5829; FStar_Ident.str = "Type0";_}
            ->
            let uu____5832 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____5832, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5847; FStar_Ident.ident = uu____5848;
              FStar_Ident.nsstr = uu____5849; FStar_Ident.str = "Type";_}
            ->
            let uu____5852 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____5852, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____5867; FStar_Ident.ident = uu____5868;
               FStar_Ident.nsstr = uu____5869; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5887 =
              let uu____5890 =
                let uu____5891 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____5891  in
              mk1 uu____5890  in
            (uu____5887, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5904; FStar_Ident.ident = uu____5905;
              FStar_Ident.nsstr = uu____5906; FStar_Ident.str = "Effect";_}
            ->
            let uu____5909 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____5909, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5924; FStar_Ident.ident = uu____5925;
              FStar_Ident.nsstr = uu____5926; FStar_Ident.str = "True";_}
            ->
            let uu____5929 =
              let uu____5930 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____5930
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____5929, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5941; FStar_Ident.ident = uu____5942;
              FStar_Ident.nsstr = uu____5943; FStar_Ident.str = "False";_}
            ->
            let uu____5946 =
              let uu____5947 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____5947
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____5946, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5960;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5962 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____5962 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____5971 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_defined_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____5971, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____5982 =
                    let uu____5983 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____5983 txt
                     in
                  failwith uu____5982))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5990 = desugar_name mk1 setpos env true l  in
              (uu____5990, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6003 = desugar_name mk1 setpos env true l  in
              (uu____6003, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____6024 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____6024 with
                | FStar_Pervasives_Native.Some uu____6033 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____6038 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____6038 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6052 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____6069 =
                    let uu____6070 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____6070  in
                  (uu____6069, noaqs)
              | uu____6081 ->
                  let uu____6088 =
                    let uu____6093 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6093)  in
                  FStar_Errors.raise_error uu____6088
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6100 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____6100 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6107 =
                    let uu____6112 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6112)
                     in
                  FStar_Errors.raise_error uu____6107
                    top.FStar_Parser_AST.range
              | uu____6117 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____6121 = desugar_name mk1 setpos env true lid'  in
                  (uu____6121, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6147 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6147 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6178 ->
                       let uu____6185 =
                         FStar_Util.take
                           (fun uu____6209  ->
                              match uu____6209 with
                              | (uu____6214,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____6185 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____6259 =
                              let uu____6274 =
                                FStar_List.map
                                  (fun uu____6307  ->
                                     match uu____6307 with
                                     | (t,imp) ->
                                         let uu____6324 =
                                           desugar_term_aq env t  in
                                         (match uu____6324 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____6274
                                FStar_List.unzip
                               in
                            (match uu____6259 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____6417 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____6417, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____6447 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____6447 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6454 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6465 =
              FStar_List.fold_left
                (fun uu____6510  ->
                   fun b  ->
                     match uu____6510 with
                     | (env1,tparams,typs) ->
                         let uu____6567 = desugar_binder env1 b  in
                         (match uu____6567 with
                          | (xopt,t1) ->
                              let uu____6596 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6605 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6605)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6596 with
                               | (env2,x) ->
                                   let uu____6625 =
                                     let uu____6628 =
                                       let uu____6631 =
                                         let uu____6632 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____6632
                                          in
                                       [uu____6631]  in
                                     FStar_List.append typs uu____6628  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___128_6658 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___128_6658.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___128_6658.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6625)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6465 with
             | (env1,uu____6686,targs) ->
                 let uu____6708 =
                   let uu____6713 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____6713
                    in
                 (match uu____6708 with
                  | (tup,uu____6723) ->
                      let uu____6724 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____6724, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____6749 = uncurry binders t  in
            (match uu____6749 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___94_6785 =
                   match uu___94_6785 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____6799 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____6799
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____6821 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____6821 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____6830 = aux env [] bs  in (uu____6830, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____6851 = desugar_binder env b  in
            (match uu____6851 with
             | (FStar_Pervasives_Native.None ,uu____6862) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____6876 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____6876 with
                  | ((x,uu____6886),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____6893 =
                        let uu____6896 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____6896  in
                      (uu____6893, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____6928 =
              FStar_List.fold_left
                (fun uu____6948  ->
                   fun pat  ->
                     match uu____6948 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____6974,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____6984 =
                                let uu____6987 = free_type_vars env1 t  in
                                FStar_List.append uu____6987 ftvs  in
                              (env1, uu____6984)
                          | FStar_Parser_AST.PatAscribed
                              (uu____6992,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____7003 =
                                let uu____7006 = free_type_vars env1 t  in
                                let uu____7009 =
                                  let uu____7012 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____7012 ftvs  in
                                FStar_List.append uu____7006 uu____7009  in
                              (env1, uu____7003)
                          | uu____7017 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____6928 with
             | (uu____7026,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____7038 =
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
                   FStar_List.append uu____7038 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___95_7083 =
                   match uu___95_7083 with
                   | [] ->
                       let uu____7106 = desugar_term_aq env1 body  in
                       (match uu____7106 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7137 =
                                      let uu____7138 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7138
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7137 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7191 =
                              let uu____7194 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7194  in
                            (uu____7191, aq))
                   | p::rest ->
                       let uu____7207 = desugar_binding_pat env1 p  in
                       (match uu____7207 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7235 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7240 =
                              match b with
                              | LetBinder uu____7273 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7329) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7365 =
                                          let uu____7370 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7370, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7365
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7406,uu____7407) ->
                                             let tup2 =
                                               let uu____7409 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7409
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7413 =
                                                 let uu____7416 =
                                                   let uu____7417 =
                                                     let uu____7432 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7435 =
                                                       let uu____7438 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7439 =
                                                         let uu____7442 =
                                                           let uu____7443 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7443
                                                            in
                                                         [uu____7442]  in
                                                       uu____7438 ::
                                                         uu____7439
                                                        in
                                                     (uu____7432, uu____7435)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7417
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7416
                                                  in
                                               uu____7413
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____7454 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7454
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____7485,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____7487,pats)) ->
                                             let tupn =
                                               let uu____7526 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7526
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7536 =
                                                 let uu____7537 =
                                                   let uu____7552 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____7555 =
                                                     let uu____7564 =
                                                       let uu____7573 =
                                                         let uu____7574 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7574
                                                          in
                                                       [uu____7573]  in
                                                     FStar_List.append args
                                                       uu____7564
                                                      in
                                                   (uu____7552, uu____7555)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____7537
                                                  in
                                               mk1 uu____7536  in
                                             let p2 =
                                               let uu____7594 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____7594
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____7629 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7240 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____7700,uu____7701,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____7719 =
                let uu____7720 = unparen e  in uu____7720.FStar_Parser_AST.tm
                 in
              match uu____7719 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____7730 ->
                  let uu____7731 = desugar_term_aq env e  in
                  (match uu____7731 with
                   | (head1,aq) ->
                       let uu____7744 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____7744, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____7751 ->
            let rec aux args aqs e =
              let uu____7804 =
                let uu____7805 = unparen e  in uu____7805.FStar_Parser_AST.tm
                 in
              match uu____7804 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____7825 = desugar_term_aq env t  in
                  (match uu____7825 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____7861 ->
                  let uu____7862 = desugar_term_aq env e  in
                  (match uu____7862 with
                   | (head1,aq) ->
                       let uu____7885 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____7885, (join_aqs (aq :: aqs))))
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
            let uu____7925 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____7925
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
            let uu____7977 = desugar_term_aq env t  in
            (match uu____7977 with
             | (tm,s) ->
                 let uu____7988 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____7988, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____7996 =
              let uu____8005 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____8005 then desugar_typ_aq else desugar_term_aq  in
            uu____7996 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8056 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8199  ->
                        match uu____8199 with
                        | (attr_opt,(p,def)) ->
                            let uu____8257 = is_app_pattern p  in
                            if uu____8257
                            then
                              let uu____8288 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8288, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____8370 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____8370, def1)
                               | uu____8415 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____8453);
                                           FStar_Parser_AST.prange =
                                             uu____8454;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____8502 =
                                            let uu____8523 =
                                              let uu____8528 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8528  in
                                            (uu____8523, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____8502, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____8619) ->
                                        if top_level
                                        then
                                          let uu____8654 =
                                            let uu____8675 =
                                              let uu____8680 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8680  in
                                            (uu____8675, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____8654, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____8770 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____8801 =
                FStar_List.fold_left
                  (fun uu____8874  ->
                     fun uu____8875  ->
                       match (uu____8874, uu____8875) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____8983,uu____8984),uu____8985))
                           ->
                           let uu____9102 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9128 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9128 with
                                  | (env2,xx) ->
                                      let uu____9147 =
                                        let uu____9150 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9150 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9147))
                             | FStar_Util.Inr l ->
                                 let uu____9158 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____9158, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9102 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____8801 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9300 =
                    match uu____9300 with
                    | (attrs_opt,(uu____9336,args,result_t),def) ->
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
                                let uu____9424 = is_comp_type env1 t  in
                                if uu____9424
                                then
                                  ((let uu____9426 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____9436 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____9436))
                                       in
                                    match uu____9426 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____9439 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____9441 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____9441))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____9439
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____9445 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____9445 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____9449 ->
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
                              let uu____9464 =
                                let uu____9465 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____9465
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____9464
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
                  let uu____9524 = desugar_term_aq env' body  in
                  (match uu____9524 with
                   | (body1,aq) ->
                       let uu____9537 =
                         let uu____9540 =
                           let uu____9541 =
                             let uu____9554 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____9554)  in
                           FStar_Syntax_Syntax.Tm_let uu____9541  in
                         FStar_All.pipe_left mk1 uu____9540  in
                       (uu____9537, aq))
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
              let uu____9614 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____9614 with
              | (env1,binder,pat1) ->
                  let uu____9636 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____9662 = desugar_term_aq env1 t2  in
                        (match uu____9662 with
                         | (body1,aq) ->
                             let fv =
                               let uu____9676 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____9676
                                 FStar_Pervasives_Native.None
                                in
                             let uu____9677 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____9677, aq))
                    | LocalBinder (x,uu____9701) ->
                        let uu____9702 = desugar_term_aq env1 t2  in
                        (match uu____9702 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____9716;
                                   FStar_Syntax_Syntax.p = uu____9717;_}::[]
                                   -> body1
                               | uu____9722 ->
                                   let uu____9725 =
                                     let uu____9728 =
                                       let uu____9729 =
                                         let uu____9752 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____9753 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____9752, uu____9753)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____9729
                                        in
                                     FStar_Syntax_Syntax.mk uu____9728  in
                                   uu____9725 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____9763 =
                               let uu____9766 =
                                 let uu____9767 =
                                   let uu____9780 =
                                     let uu____9781 =
                                       let uu____9782 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____9782]  in
                                     FStar_Syntax_Subst.close uu____9781
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____9780)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____9767  in
                               FStar_All.pipe_left mk1 uu____9766  in
                             (uu____9763, aq))
                     in
                  (match uu____9636 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____9823 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____9823, aq)
                       else (tm, aq))
               in
            let uu____9835 = FStar_List.hd lbs  in
            (match uu____9835 with
             | (attrs,(head_pat,defn)) ->
                 let uu____9879 = is_rec || (is_app_pattern head_pat)  in
                 if uu____9879
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____9892 =
                let uu____9893 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____9893  in
              mk1 uu____9892  in
            let uu____9894 = desugar_term_aq env t1  in
            (match uu____9894 with
             | (t1',aq1) ->
                 let uu____9905 = desugar_term_aq env t2  in
                 (match uu____9905 with
                  | (t2',aq2) ->
                      let uu____9916 = desugar_term_aq env t3  in
                      (match uu____9916 with
                       | (t3',aq3) ->
                           let uu____9927 =
                             let uu____9930 =
                               let uu____9931 =
                                 let uu____9954 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None)
                                    in
                                 let uu____9975 =
                                   let uu____9990 =
                                     let uu____10003 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____10003,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____10014 =
                                     let uu____10029 =
                                       let uu____10042 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____10042,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____10029]  in
                                   uu____9990 :: uu____10014  in
                                 (uu____9954, uu____9975)  in
                               FStar_Syntax_Syntax.Tm_match uu____9931  in
                             mk1 uu____9930  in
                           (uu____9927, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10201 =
              match uu____10201 with
              | (pat,wopt,b) ->
                  let uu____10223 = desugar_match_pat env pat  in
                  (match uu____10223 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____10248 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____10248
                          in
                       let uu____10249 = desugar_term_aq env1 b  in
                       (match uu____10249 with
                        | (b1,aq) ->
                            let uu____10262 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____10262, aq)))
               in
            let uu____10267 = desugar_term_aq env e  in
            (match uu____10267 with
             | (e1,aq) ->
                 let uu____10278 =
                   let uu____10287 =
                     let uu____10298 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____10298 FStar_List.unzip  in
                   FStar_All.pipe_right uu____10287
                     (fun uu____10362  ->
                        match uu____10362 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____10278 with
                  | (brs,aqs) ->
                      let uu____10413 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____10413, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____10446 = is_comp_type env t  in
              if uu____10446
              then
                let uu____10453 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____10453
              else
                (let uu____10459 = desugar_term env t  in
                 FStar_Util.Inl uu____10459)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____10465 = desugar_term_aq env e  in
            (match uu____10465 with
             | (e1,aq) ->
                 let uu____10476 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____10476, aq))
        | FStar_Parser_AST.Record (uu____10505,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____10546 = FStar_List.hd fields  in
              match uu____10546 with | (f,uu____10558) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____10600  ->
                        match uu____10600 with
                        | (g,uu____10606) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____10612,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____10626 =
                         let uu____10631 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____10631)
                          in
                       FStar_Errors.raise_error uu____10626
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
                  let uu____10639 =
                    let uu____10650 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____10681  ->
                              match uu____10681 with
                              | (f,uu____10691) ->
                                  let uu____10692 =
                                    let uu____10693 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____10693
                                     in
                                  (uu____10692, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____10650)  in
                  FStar_Parser_AST.Construct uu____10639
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____10711 =
                      let uu____10712 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____10712  in
                    FStar_Parser_AST.mk_term uu____10711
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____10714 =
                      let uu____10727 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____10757  ->
                                match uu____10757 with
                                | (f,uu____10767) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____10727)  in
                    FStar_Parser_AST.Record uu____10714  in
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
            let uu____10827 = desugar_term_aq env recterm1  in
            (match uu____10827 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____10843;
                         FStar_Syntax_Syntax.vars = uu____10844;_},args)
                      ->
                      let uu____10866 =
                        let uu____10869 =
                          let uu____10870 =
                            let uu____10885 =
                              let uu____10886 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____10887 =
                                let uu____10890 =
                                  let uu____10891 =
                                    let uu____10898 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____10898)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____10891
                                   in
                                FStar_Pervasives_Native.Some uu____10890  in
                              FStar_Syntax_Syntax.fvar uu____10886
                                FStar_Syntax_Syntax.Delta_constant
                                uu____10887
                               in
                            (uu____10885, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____10870  in
                        FStar_All.pipe_left mk1 uu____10869  in
                      (uu____10866, s)
                  | uu____10927 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____10931 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____10931 with
              | (constrname,is_rec) ->
                  let uu____10946 = desugar_term_aq env e  in
                  (match uu____10946 with
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
                       let uu____10964 =
                         let uu____10967 =
                           let uu____10968 =
                             let uu____10983 =
                               let uu____10984 =
                                 let uu____10985 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____10985
                                  in
                               FStar_Syntax_Syntax.fvar uu____10984
                                 FStar_Syntax_Syntax.Delta_equational qual
                                in
                             let uu____10986 =
                               let uu____10989 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____10989]  in
                             (uu____10983, uu____10986)  in
                           FStar_Syntax_Syntax.Tm_app uu____10968  in
                         FStar_All.pipe_left mk1 uu____10967  in
                       (uu____10964, s))))
        | FStar_Parser_AST.NamedTyp (uu____10996,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____11005 =
              let uu____11006 = FStar_Syntax_Subst.compress tm  in
              uu____11006.FStar_Syntax_Syntax.n  in
            (match uu____11005 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____11014 =
                   let uu___129_11017 =
                     let uu____11018 =
                       let uu____11019 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____11019  in
                     FStar_Syntax_Util.exp_string uu____11018  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___129_11017.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___129_11017.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____11014, noaqs)
             | uu____11032 ->
                 let uu____11033 =
                   let uu____11038 =
                     let uu____11039 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____11039
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____11038)  in
                 FStar_Errors.raise_error uu____11033
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____11045 = desugar_term_aq env e  in
            (match uu____11045 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____11057 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____11057, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____11077 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____11078 =
              let uu____11087 =
                let uu____11094 = desugar_term env e  in (bv, b, uu____11094)
                 in
              [uu____11087]  in
            (uu____11077, uu____11078)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____11125 =
              let uu____11128 =
                let uu____11129 =
                  let uu____11136 = desugar_term env e  in (uu____11136, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____11129  in
              FStar_All.pipe_left mk1 uu____11128  in
            (uu____11125, noaqs)
        | uu____11151 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____11152 = desugar_formula env top  in
            (uu____11152, noaqs)
        | uu____11163 ->
            let uu____11164 =
              let uu____11169 =
                let uu____11170 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____11170  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____11169)  in
            FStar_Errors.raise_error uu____11164 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____11176 -> false
    | uu____11185 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____11191 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____11191 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____11195 -> false

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
           (fun uu____11232  ->
              match uu____11232 with
              | (a,imp) ->
                  let uu____11245 = desugar_term env a  in
                  arg_withimp_e imp uu____11245))

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
        let is_requires uu____11271 =
          match uu____11271 with
          | (t1,uu____11277) ->
              let uu____11278 =
                let uu____11279 = unparen t1  in
                uu____11279.FStar_Parser_AST.tm  in
              (match uu____11278 with
               | FStar_Parser_AST.Requires uu____11280 -> true
               | uu____11287 -> false)
           in
        let is_ensures uu____11295 =
          match uu____11295 with
          | (t1,uu____11301) ->
              let uu____11302 =
                let uu____11303 = unparen t1  in
                uu____11303.FStar_Parser_AST.tm  in
              (match uu____11302 with
               | FStar_Parser_AST.Ensures uu____11304 -> true
               | uu____11311 -> false)
           in
        let is_app head1 uu____11322 =
          match uu____11322 with
          | (t1,uu____11328) ->
              let uu____11329 =
                let uu____11330 = unparen t1  in
                uu____11330.FStar_Parser_AST.tm  in
              (match uu____11329 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____11332;
                      FStar_Parser_AST.level = uu____11333;_},uu____11334,uu____11335)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____11336 -> false)
           in
        let is_smt_pat uu____11344 =
          match uu____11344 with
          | (t1,uu____11350) ->
              let uu____11351 =
                let uu____11352 = unparen t1  in
                uu____11352.FStar_Parser_AST.tm  in
              (match uu____11351 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____11355);
                             FStar_Parser_AST.range = uu____11356;
                             FStar_Parser_AST.level = uu____11357;_},uu____11358)::uu____11359::[])
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
                             FStar_Parser_AST.range = uu____11398;
                             FStar_Parser_AST.level = uu____11399;_},uu____11400)::uu____11401::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____11426 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____11454 = head_and_args t1  in
          match uu____11454 with
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
                   let thunk_ens uu____11548 =
                     match uu____11548 with
                     | (e,i) ->
                         let uu____11559 = thunk_ens_ e  in (uu____11559, i)
                      in
                   let fail_lemma uu____11569 =
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
                         let uu____11649 =
                           let uu____11656 =
                             let uu____11663 = thunk_ens ens  in
                             [uu____11663; nil_pat]  in
                           req_true :: uu____11656  in
                         unit_tm :: uu____11649
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____11710 =
                           let uu____11717 =
                             let uu____11724 = thunk_ens ens  in
                             [uu____11724; nil_pat]  in
                           req :: uu____11717  in
                         unit_tm :: uu____11710
                     | ens::smtpat::[] when
                         (((let uu____11773 = is_requires ens  in
                            Prims.op_Negation uu____11773) &&
                             (let uu____11775 = is_smt_pat ens  in
                              Prims.op_Negation uu____11775))
                            &&
                            (let uu____11777 = is_decreases ens  in
                             Prims.op_Negation uu____11777))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____11778 =
                           let uu____11785 =
                             let uu____11792 = thunk_ens ens  in
                             [uu____11792; smtpat]  in
                           req_true :: uu____11785  in
                         unit_tm :: uu____11778
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____11839 =
                           let uu____11846 =
                             let uu____11853 = thunk_ens ens  in
                             [uu____11853; nil_pat; dec]  in
                           req_true :: uu____11846  in
                         unit_tm :: uu____11839
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____11913 =
                           let uu____11920 =
                             let uu____11927 = thunk_ens ens  in
                             [uu____11927; smtpat; dec]  in
                           req_true :: uu____11920  in
                         unit_tm :: uu____11913
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____11987 =
                           let uu____11994 =
                             let uu____12001 = thunk_ens ens  in
                             [uu____12001; nil_pat; dec]  in
                           req :: uu____11994  in
                         unit_tm :: uu____11987
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12061 =
                           let uu____12068 =
                             let uu____12075 = thunk_ens ens  in
                             [uu____12075; smtpat]  in
                           req :: uu____12068  in
                         unit_tm :: uu____12061
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____12140 =
                           let uu____12147 =
                             let uu____12154 = thunk_ens ens  in
                             [uu____12154; dec; smtpat]  in
                           req :: uu____12147  in
                         unit_tm :: uu____12140
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____12216 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____12216, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12244 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12244
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____12245 =
                     let uu____12252 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12252, [])  in
                   (uu____12245, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12270 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12270
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____12271 =
                     let uu____12278 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12278, [])  in
                   (uu____12271, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____12294 =
                     let uu____12301 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12301, [])  in
                   (uu____12294, [(t1, FStar_Parser_AST.Nothing)])
               | uu____12324 ->
                   let default_effect =
                     let uu____12326 = FStar_Options.ml_ish ()  in
                     if uu____12326
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____12329 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____12329
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____12331 =
                     let uu____12338 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12338, [])  in
                   (uu____12331, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____12361 = pre_process_comp_typ t  in
        match uu____12361 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____12410 =
                       let uu____12415 =
                         let uu____12416 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____12416
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____12415)
                        in
                     fail1 () uu____12410)
                else Obj.repr ());
             (let is_universe uu____12425 =
                match uu____12425 with
                | (uu____12430,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____12432 = FStar_Util.take is_universe args  in
              match uu____12432 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____12491  ->
                         match uu____12491 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____12498 =
                    let uu____12513 = FStar_List.hd args1  in
                    let uu____12522 = FStar_List.tl args1  in
                    (uu____12513, uu____12522)  in
                  (match uu____12498 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____12577 =
                         let is_decrease uu____12613 =
                           match uu____12613 with
                           | (t1,uu____12623) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____12633;
                                       FStar_Syntax_Syntax.vars = uu____12634;_},uu____12635::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____12666 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____12577 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____12780  ->
                                      match uu____12780 with
                                      | (t1,uu____12790) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____12799,(arg,uu____12801)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____12830 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____12843 -> false  in
                              (((is_empty () (Obj.magic decreases_clause)) &&
                                  (is_empty () (Obj.magic rest2)))
                                 && (is_empty () (Obj.magic cattributes)))
                                && (is_empty () (Obj.magic universes1))
                               in
                            let uu____12846 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____12846
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____12850 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____12850
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____12857 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____12857
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____12861 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____12861
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____12865 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____12865
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____12869 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____12869
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____12887 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____12887
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
                                                  let uu____12976 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____12976
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
                                            | uu____12991 -> pat  in
                                          let uu____12992 =
                                            let uu____13003 =
                                              let uu____13014 =
                                                let uu____13023 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____13023, aq)  in
                                              [uu____13014]  in
                                            ens :: uu____13003  in
                                          req :: uu____12992
                                      | uu____13064 -> rest2
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
        | uu____13086 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___130_13103 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___130_13103.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___130_13103.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___131_13137 = b  in
             {
               FStar_Parser_AST.b = (uu___131_13137.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___131_13137.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___131_13137.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____13196 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____13196)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____13209 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____13209 with
             | (env1,a1) ->
                 let a2 =
                   let uu___132_13219 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___132_13219.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___132_13219.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____13241 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____13255 =
                     let uu____13258 =
                       let uu____13259 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____13259]  in
                     no_annot_abs uu____13258 body2  in
                   FStar_All.pipe_left setpos uu____13255  in
                 let uu____13264 =
                   let uu____13265 =
                     let uu____13280 =
                       let uu____13281 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____13281
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____13282 =
                       let uu____13285 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____13285]  in
                     (uu____13280, uu____13282)  in
                   FStar_Syntax_Syntax.Tm_app uu____13265  in
                 FStar_All.pipe_left mk1 uu____13264)
        | uu____13290 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____13362 = q (rest, pats, body)  in
              let uu____13369 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____13362 uu____13369
                FStar_Parser_AST.Formula
               in
            let uu____13370 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____13370 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____13379 -> failwith "impossible"  in
      let uu____13382 =
        let uu____13383 = unparen f  in uu____13383.FStar_Parser_AST.tm  in
      match uu____13382 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____13390,uu____13391) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____13402,uu____13403) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13434 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____13434
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13470 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____13470
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____13513 -> desugar_term env f

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
      let uu____13518 =
        FStar_List.fold_left
          (fun uu____13554  ->
             fun b  ->
               match uu____13554 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___133_13606 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___133_13606.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___133_13606.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___133_13606.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____13623 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____13623 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___134_13643 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___134_13643.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___134_13643.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____13660 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____13518 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____13747 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____13747)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____13752 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____13752)
      | FStar_Parser_AST.TVariable x ->
          let uu____13756 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____13756)
      | FStar_Parser_AST.NoName t ->
          let uu____13764 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____13764)
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
               (fun uu___96_13797  ->
                  match uu___96_13797 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____13798 -> false))
           in
        let quals2 q =
          let uu____13809 =
            (let uu____13812 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____13812) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____13809
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____13826 = FStar_Ident.range_of_lid disc_name  in
                let uu____13827 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____13826;
                  FStar_Syntax_Syntax.sigquals = uu____13827;
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
            let uu____13858 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____13888  ->
                        match uu____13888 with
                        | (x,uu____13896) ->
                            let uu____13897 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____13897 with
                             | (field_name,uu____13905) ->
                                 let only_decl =
                                   ((let uu____13909 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____13909)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____13911 =
                                        let uu____13912 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____13912.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____13911)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____13926 =
                                       FStar_List.filter
                                         (fun uu___97_13930  ->
                                            match uu___97_13930 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____13931 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____13926
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___98_13944  ->
                                             match uu___98_13944 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____13945 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____13947 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____13947;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____13954 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____13954
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____13959 =
                                        let uu____13964 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____13964  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____13959;
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
                                      let uu____13968 =
                                        let uu____13969 =
                                          let uu____13976 =
                                            let uu____13979 =
                                              let uu____13980 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____13980
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____13979]  in
                                          ((false, [lb]), uu____13976)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____13969
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____13968;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____13858 FStar_List.flatten
  
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
            (lid,uu____14024,t,uu____14026,n1,uu____14028) when
            let uu____14033 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____14033 ->
            let uu____14034 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____14034 with
             | (formals,uu____14050) ->
                 (match formals with
                  | [] -> []
                  | uu____14073 ->
                      let filter_records uu___99_14085 =
                        match uu___99_14085 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____14088,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____14100 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____14102 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____14102 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____14112 = FStar_Util.first_N n1 formals  in
                      (match uu____14112 with
                       | (uu____14135,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____14161 -> []
  
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
                    let uu____14211 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____14211
                    then
                      let uu____14214 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____14214
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____14217 =
                      let uu____14222 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____14222  in
                    let uu____14223 =
                      let uu____14226 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____14226  in
                    let uu____14229 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____14217;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____14223;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____14229;
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
          let tycon_id uu___100_14276 =
            match uu___100_14276 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____14278,uu____14279) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____14289,uu____14290,uu____14291) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____14301,uu____14302,uu____14303) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____14333,uu____14334,uu____14335) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____14377) ->
                let uu____14378 =
                  let uu____14379 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14379  in
                FStar_Parser_AST.mk_term uu____14378 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____14381 =
                  let uu____14382 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14382  in
                FStar_Parser_AST.mk_term uu____14381 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____14384) ->
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
              | uu____14407 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____14413 =
                     let uu____14414 =
                       let uu____14421 = binder_to_term b  in
                       (out, uu____14421, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____14414  in
                   FStar_Parser_AST.mk_term uu____14413
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___101_14431 =
            match uu___101_14431 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____14487  ->
                       match uu____14487 with
                       | (x,t,uu____14498) ->
                           let uu____14503 =
                             let uu____14504 =
                               let uu____14509 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____14509, t)  in
                             FStar_Parser_AST.Annotated uu____14504  in
                           FStar_Parser_AST.mk_binder uu____14503
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____14511 =
                    let uu____14512 =
                      let uu____14513 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____14513  in
                    FStar_Parser_AST.mk_term uu____14512
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____14511 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____14517 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____14544  ->
                          match uu____14544 with
                          | (x,uu____14554,uu____14555) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____14517)
            | uu____14608 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___102_14639 =
            match uu___102_14639 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____14663 = typars_of_binders _env binders  in
                (match uu____14663 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____14709 =
                         let uu____14710 =
                           let uu____14711 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____14711  in
                         FStar_Parser_AST.mk_term uu____14710
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____14709 binders  in
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
            | uu____14724 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____14768 =
              FStar_List.fold_left
                (fun uu____14808  ->
                   fun uu____14809  ->
                     match (uu____14808, uu____14809) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____14900 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____14900 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____14768 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____15013 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____15013
                | uu____15014 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____15022 = desugar_abstract_tc quals env [] tc  in
              (match uu____15022 with
               | (uu____15035,uu____15036,se,uu____15038) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____15041,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____15058 =
                                 let uu____15059 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____15059  in
                               if uu____15058
                               then
                                 let uu____15060 =
                                   let uu____15065 =
                                     let uu____15066 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____15066
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____15065)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____15060
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
                           | uu____15073 ->
                               let uu____15074 =
                                 let uu____15077 =
                                   let uu____15078 =
                                     let uu____15091 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____15091)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____15078
                                    in
                                 FStar_Syntax_Syntax.mk uu____15077  in
                               uu____15074 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___135_15095 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___135_15095.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___135_15095.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___135_15095.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____15098 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____15101 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____15101
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____15116 = typars_of_binders env binders  in
              (match uu____15116 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15152 =
                           FStar_Util.for_some
                             (fun uu___103_15154  ->
                                match uu___103_15154 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____15155 -> false) quals
                            in
                         if uu____15152
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____15162 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___104_15166  ->
                               match uu___104_15166 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____15167 -> false))
                        in
                     if uu____15162
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____15176 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____15176
                     then
                       let uu____15179 =
                         let uu____15186 =
                           let uu____15187 = unparen t  in
                           uu____15187.FStar_Parser_AST.tm  in
                         match uu____15186 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____15208 =
                               match FStar_List.rev args with
                               | (last_arg,uu____15238)::args_rev ->
                                   let uu____15250 =
                                     let uu____15251 = unparen last_arg  in
                                     uu____15251.FStar_Parser_AST.tm  in
                                   (match uu____15250 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____15279 -> ([], args))
                               | uu____15288 -> ([], args)  in
                             (match uu____15208 with
                              | (cattributes,args1) ->
                                  let uu____15327 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____15327))
                         | uu____15338 -> (t, [])  in
                       match uu____15179 with
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
                                  (fun uu___105_15360  ->
                                     match uu___105_15360 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____15361 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____15372)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____15396 = tycon_record_as_variant trec  in
              (match uu____15396 with
               | (t,fs) ->
                   let uu____15413 =
                     let uu____15416 =
                       let uu____15417 =
                         let uu____15426 =
                           let uu____15429 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____15429  in
                         (uu____15426, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____15417  in
                     uu____15416 :: quals  in
                   desugar_tycon env d uu____15413 [t])
          | uu____15434::uu____15435 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____15596 = et  in
                match uu____15596 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____15821 ->
                         let trec = tc  in
                         let uu____15845 = tycon_record_as_variant trec  in
                         (match uu____15845 with
                          | (t,fs) ->
                              let uu____15904 =
                                let uu____15907 =
                                  let uu____15908 =
                                    let uu____15917 =
                                      let uu____15920 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____15920  in
                                    (uu____15917, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____15908
                                   in
                                uu____15907 :: quals1  in
                              collect_tcs uu____15904 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____16007 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16007 with
                          | (env2,uu____16067,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____16216 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16216 with
                          | (env2,uu____16276,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____16401 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____16448 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____16448 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___107_16959  ->
                             match uu___107_16959 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____17026,uu____17027);
                                    FStar_Syntax_Syntax.sigrng = uu____17028;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____17029;
                                    FStar_Syntax_Syntax.sigmeta = uu____17030;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17031;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____17092 =
                                     typars_of_binders env1 binders  in
                                   match uu____17092 with
                                   | (env2,tpars1) ->
                                       let uu____17123 =
                                         push_tparams env2 tpars1  in
                                       (match uu____17123 with
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
                                 let uu____17156 =
                                   let uu____17177 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____17177)
                                    in
                                 [uu____17156]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____17245);
                                    FStar_Syntax_Syntax.sigrng = uu____17246;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____17248;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17249;_},constrs,tconstr,quals1)
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
                                 let uu____17345 = push_tparams env1 tpars
                                    in
                                 (match uu____17345 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____17422  ->
                                             match uu____17422 with
                                             | (x,uu____17436) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____17444 =
                                        let uu____17473 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____17587  ->
                                                  match uu____17587 with
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
                                                        let uu____17643 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____17643
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
                                                                uu___106_17654
                                                                 ->
                                                                match uu___106_17654
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____17666
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____17674 =
                                                        let uu____17695 =
                                                          let uu____17696 =
                                                            let uu____17697 =
                                                              let uu____17712
                                                                =
                                                                let uu____17715
                                                                  =
                                                                  let uu____17718
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____17718
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____17715
                                                                 in
                                                              (name, univs1,
                                                                uu____17712,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____17697
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____17696;
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
                                                          uu____17695)
                                                         in
                                                      (name, uu____17674)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____17473
                                         in
                                      (match uu____17444 with
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
                             | uu____17957 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18089  ->
                             match uu____18089 with
                             | (name_doc,uu____18117,uu____18118) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18198  ->
                             match uu____18198 with
                             | (uu____18219,uu____18220,se) -> se))
                      in
                   let uu____18250 =
                     let uu____18257 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____18257 rng
                      in
                   (match uu____18250 with
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
                               (fun uu____18323  ->
                                  match uu____18323 with
                                  | (uu____18346,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____18397,tps,k,uu____18400,constrs)
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
                                  | uu____18419 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____18436  ->
                                 match uu____18436 with
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
      let uu____18471 =
        FStar_List.fold_left
          (fun uu____18494  ->
             fun b  ->
               match uu____18494 with
               | (env1,binders1) ->
                   let uu____18514 = desugar_binder env1 b  in
                   (match uu____18514 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18531 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____18531 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____18548 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____18471 with
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
          let uu____18593 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___108_18598  ->
                    match uu___108_18598 with
                    | FStar_Syntax_Syntax.Reflectable uu____18599 -> true
                    | uu____18600 -> false))
             in
          if uu____18593
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____18603 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____18603
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
                  let uu____18707 = desugar_binders monad_env eff_binders  in
                  match uu____18707 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____18728 =
                          let uu____18729 =
                            let uu____18736 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____18736  in
                          FStar_List.length uu____18729  in
                        uu____18728 = (Prims.parse_int "1")  in
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
                            (uu____18778,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____18780,uu____18781,uu____18782),uu____18783)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____18816 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____18817 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____18829 = name_of_eff_decl decl  in
                             FStar_List.mem uu____18829 mandatory_members)
                          eff_decls
                         in
                      (match uu____18817 with
                       | (mandatory_members_decls,actions) ->
                           let uu____18846 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____18875  ->
                                     fun decl  ->
                                       match uu____18875 with
                                       | (env2,out) ->
                                           let uu____18895 =
                                             desugar_decl env2 decl  in
                                           (match uu____18895 with
                                            | (env3,ses) ->
                                                let uu____18908 =
                                                  let uu____18911 =
                                                    FStar_List.hd ses  in
                                                  uu____18911 :: out  in
                                                (env3, uu____18908)))
                                  (env1, []))
                              in
                           (match uu____18846 with
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
                                              (uu____18979,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____18982,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____18983,
                                                                  (def,uu____18985)::
                                                                  (cps_type,uu____18987)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____18988;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____18989;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____19041 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19041 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19061 =
                                                     let uu____19062 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19063 =
                                                       let uu____19064 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19064
                                                        in
                                                     let uu____19069 =
                                                       let uu____19070 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19070
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19062;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19063;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____19069
                                                     }  in
                                                   (uu____19061, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____19077,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____19080,defn),doc1)::[])
                                              when for_free ->
                                              let uu____19115 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19115 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19135 =
                                                     let uu____19136 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19137 =
                                                       let uu____19138 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19138
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19136;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19137;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____19135, doc1))
                                          | uu____19145 ->
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
                                    let uu____19175 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____19175
                                     in
                                  let uu____19176 =
                                    let uu____19177 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____19177
                                     in
                                  ([], uu____19176)  in
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
                                      let uu____19194 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____19194)  in
                                    let uu____19201 =
                                      let uu____19202 =
                                        let uu____19203 =
                                          let uu____19204 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19204
                                           in
                                        let uu____19213 = lookup1 "return"
                                           in
                                        let uu____19214 = lookup1 "bind"  in
                                        let uu____19215 =
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
                                            uu____19203;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____19213;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____19214;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____19215
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____19202
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____19201;
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
                                         (fun uu___109_19221  ->
                                            match uu___109_19221 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____19222 -> true
                                            | uu____19223 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____19233 =
                                       let uu____19234 =
                                         let uu____19235 =
                                           lookup1 "return_wp"  in
                                         let uu____19236 = lookup1 "bind_wp"
                                            in
                                         let uu____19237 =
                                           lookup1 "if_then_else"  in
                                         let uu____19238 = lookup1 "ite_wp"
                                            in
                                         let uu____19239 = lookup1 "stronger"
                                            in
                                         let uu____19240 = lookup1 "close_wp"
                                            in
                                         let uu____19241 = lookup1 "assert_p"
                                            in
                                         let uu____19242 = lookup1 "assume_p"
                                            in
                                         let uu____19243 = lookup1 "null_wp"
                                            in
                                         let uu____19244 = lookup1 "trivial"
                                            in
                                         let uu____19245 =
                                           if rr
                                           then
                                             let uu____19246 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____19246
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____19262 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____19264 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____19266 =
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
                                             uu____19235;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____19236;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____19237;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____19238;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____19239;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____19240;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____19241;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____19242;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____19243;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____19244;
                                           FStar_Syntax_Syntax.repr =
                                             uu____19245;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____19262;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____19264;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____19266
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____19234
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____19233;
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
                                          fun uu____19292  ->
                                            match uu____19292 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____19306 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____19306
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
                let uu____19330 = desugar_binders env1 eff_binders  in
                match uu____19330 with
                | (env2,binders) ->
                    let uu____19349 =
                      let uu____19368 = head_and_args defn  in
                      match uu____19368 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____19413 ->
                                let uu____19414 =
                                  let uu____19419 =
                                    let uu____19420 =
                                      let uu____19421 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____19421 " not found"
                                       in
                                    Prims.strcat "Effect " uu____19420  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____19419)
                                   in
                                FStar_Errors.raise_error uu____19414
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____19423 =
                            match FStar_List.rev args with
                            | (last_arg,uu____19453)::args_rev ->
                                let uu____19465 =
                                  let uu____19466 = unparen last_arg  in
                                  uu____19466.FStar_Parser_AST.tm  in
                                (match uu____19465 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____19494 -> ([], args))
                            | uu____19503 -> ([], args)  in
                          (match uu____19423 with
                           | (cattributes,args1) ->
                               let uu____19554 = desugar_args env2 args1  in
                               let uu____19563 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____19554, uu____19563))
                       in
                    (match uu____19349 with
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
                          (let uu____19619 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____19619 with
                           | (ed_binders,uu____19633,ed_binders_opening) ->
                               let sub1 uu____19644 =
                                 match uu____19644 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____19658 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____19658 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____19662 =
                                       let uu____19663 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____19663)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____19662
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____19668 =
                                   let uu____19669 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____19669
                                    in
                                 let uu____19680 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____19681 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____19682 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____19683 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____19684 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____19685 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____19686 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____19687 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____19688 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____19689 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____19690 =
                                   let uu____19691 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____19691
                                    in
                                 let uu____19702 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____19703 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____19704 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____19712 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____19713 =
                                          let uu____19714 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19714
                                           in
                                        let uu____19725 =
                                          let uu____19726 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19726
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____19712;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____19713;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____19725
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
                                     uu____19668;
                                   FStar_Syntax_Syntax.ret_wp = uu____19680;
                                   FStar_Syntax_Syntax.bind_wp = uu____19681;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____19682;
                                   FStar_Syntax_Syntax.ite_wp = uu____19683;
                                   FStar_Syntax_Syntax.stronger = uu____19684;
                                   FStar_Syntax_Syntax.close_wp = uu____19685;
                                   FStar_Syntax_Syntax.assert_p = uu____19686;
                                   FStar_Syntax_Syntax.assume_p = uu____19687;
                                   FStar_Syntax_Syntax.null_wp = uu____19688;
                                   FStar_Syntax_Syntax.trivial = uu____19689;
                                   FStar_Syntax_Syntax.repr = uu____19690;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____19702;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____19703;
                                   FStar_Syntax_Syntax.actions = uu____19704;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____19739 =
                                     let uu____19740 =
                                       let uu____19747 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____19747
                                        in
                                     FStar_List.length uu____19740  in
                                   uu____19739 = (Prims.parse_int "1")  in
                                 let uu____19776 =
                                   let uu____19779 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____19779 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____19776;
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
                                             let uu____19799 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____19799
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____19801 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____19801
                                 then
                                   let reflect_lid =
                                     let uu____19805 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____19805
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
    let uu____19817 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____19817 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____19868 ->
              let uu____19869 =
                let uu____19870 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____19870
                 in
              Prims.strcat "\n  " uu____19869
          | uu____19871 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____19884  ->
               match uu____19884 with
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
          let uu____19902 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____19902
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____19904 =
          let uu____19913 = FStar_Syntax_Syntax.as_arg arg  in [uu____19913]
           in
        FStar_Syntax_Util.mk_app fv uu____19904

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____19920 = desugar_decl_noattrs env d  in
      match uu____19920 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____19940 = mk_comment_attr d  in uu____19940 :: attrs1  in
          let s =
            FStar_List.fold_left
              (fun s  ->
                 fun a  ->
                   let uu____19951 =
                     let uu____19952 = FStar_Syntax_Print.term_to_string a
                        in
                     Prims.strcat "; " uu____19952  in
                   Prims.strcat s uu____19951) "" attrs2
             in
          let uu____19953 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___136_19959 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___136_19959.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___136_19959.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___136_19959.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___136_19959.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____19953)

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
      | FStar_Parser_AST.Fsdoc uu____19985 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____20001 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____20001, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____20040  ->
                 match uu____20040 with | (x,uu____20048) -> x) tcs
             in
          let uu____20053 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____20053 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____20075;
                    FStar_Parser_AST.prange = uu____20076;_},uu____20077)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____20086;
                    FStar_Parser_AST.prange = uu____20087;_},uu____20088)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____20103;
                         FStar_Parser_AST.prange = uu____20104;_},uu____20105);
                    FStar_Parser_AST.prange = uu____20106;_},uu____20107)::[]
                   -> false
               | (p,uu____20135)::[] ->
                   let uu____20144 = is_app_pattern p  in
                   Prims.op_Negation uu____20144
               | uu____20145 -> false)
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
            let uu____20218 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____20218 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____20230 =
                     let uu____20231 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____20231.FStar_Syntax_Syntax.n  in
                   match uu____20230 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____20239) ->
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
                         | uu____20272::uu____20273 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____20276 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___110_20291  ->
                                     match uu___110_20291 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____20294;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20295;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20296;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20297;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20298;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20299;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20300;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20312;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20313;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20314;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20315;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20316;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20317;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____20331 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____20362  ->
                                   match uu____20362 with
                                   | (uu____20375,(uu____20376,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____20331
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____20400 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____20400
                         then
                           let uu____20409 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___137_20423 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___138_20425 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___138_20425.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___138_20425.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___137_20423.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___137_20423.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___137_20423.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___137_20423.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___137_20423.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___137_20423.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____20409)
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
                   | uu____20460 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____20466 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____20485 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____20466 with
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
                       let uu___139_20521 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___139_20521.FStar_Parser_AST.prange)
                       }
                   | uu____20528 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___140_20535 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___140_20535.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___140_20535.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___140_20535.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____20567 id1 =
                   match uu____20567 with
                   | (env1,ses) ->
                       let main =
                         let uu____20588 =
                           let uu____20589 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____20589  in
                         FStar_Parser_AST.mk_term uu____20588
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
                       let uu____20639 = desugar_decl env1 id_decl  in
                       (match uu____20639 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____20657 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____20657 FStar_Util.set_elements
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
            let uu____20688 = close_fun env t  in
            desugar_term env uu____20688  in
          let quals1 =
            let uu____20692 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____20692
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____20698 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____20698;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____20710 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____20710 with
           | (t,uu____20724) ->
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
            let uu____20758 =
              let uu____20765 = FStar_Syntax_Syntax.null_binder t  in
              [uu____20765]  in
            let uu____20766 =
              let uu____20769 =
                let uu____20770 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____20770  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____20769
               in
            FStar_Syntax_Util.arrow uu____20758 uu____20766  in
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
            let uu____20833 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____20833 with
            | FStar_Pervasives_Native.None  ->
                let uu____20836 =
                  let uu____20841 =
                    let uu____20842 =
                      let uu____20843 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____20843 " not found"  in
                    Prims.strcat "Effect name " uu____20842  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____20841)  in
                FStar_Errors.raise_error uu____20836
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____20847 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____20889 =
                  let uu____20898 =
                    let uu____20905 = desugar_term env t  in
                    ([], uu____20905)  in
                  FStar_Pervasives_Native.Some uu____20898  in
                (uu____20889, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____20938 =
                  let uu____20947 =
                    let uu____20954 = desugar_term env wp  in
                    ([], uu____20954)  in
                  FStar_Pervasives_Native.Some uu____20947  in
                let uu____20963 =
                  let uu____20972 =
                    let uu____20979 = desugar_term env t  in
                    ([], uu____20979)  in
                  FStar_Pervasives_Native.Some uu____20972  in
                (uu____20938, uu____20963)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____21005 =
                  let uu____21014 =
                    let uu____21021 = desugar_term env t  in
                    ([], uu____21021)  in
                  FStar_Pervasives_Native.Some uu____21014  in
                (FStar_Pervasives_Native.None, uu____21005)
             in
          (match uu____20847 with
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
            let uu____21101 =
              let uu____21102 =
                let uu____21109 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____21109, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____21102  in
            {
              FStar_Syntax_Syntax.sigel = uu____21101;
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
      let uu____21133 =
        FStar_List.fold_left
          (fun uu____21153  ->
             fun d  ->
               match uu____21153 with
               | (env1,sigelts) ->
                   let uu____21173 = desugar_decl env1 d  in
                   (match uu____21173 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____21133 with
      | (env1,sigelts) ->
          let rec forward acc uu___112_21214 =
            match uu___112_21214 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____21228,FStar_Syntax_Syntax.Sig_let uu____21229) ->
                     let uu____21242 =
                       let uu____21245 =
                         let uu___141_21246 = se2  in
                         let uu____21247 =
                           let uu____21250 =
                             FStar_List.filter
                               (fun uu___111_21264  ->
                                  match uu___111_21264 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____21268;
                                           FStar_Syntax_Syntax.vars =
                                             uu____21269;_},uu____21270);
                                      FStar_Syntax_Syntax.pos = uu____21271;
                                      FStar_Syntax_Syntax.vars = uu____21272;_}
                                      when
                                      let uu____21295 =
                                        let uu____21296 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____21296
                                         in
                                      uu____21295 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____21297 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____21250
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___141_21246.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___141_21246.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___141_21246.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___141_21246.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____21247
                         }  in
                       uu____21245 :: se1 :: acc  in
                     forward uu____21242 sigelts1
                 | uu____21302 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____21310 = forward [] sigelts  in (env1, uu____21310)
  
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
          | (FStar_Pervasives_Native.None ,uu____21361) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____21365;
               FStar_Syntax_Syntax.exports = uu____21366;
               FStar_Syntax_Syntax.is_interface = uu____21367;_},FStar_Parser_AST.Module
             (current_lid,uu____21369)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____21377) ->
              let uu____21380 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____21380
           in
        let uu____21385 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____21421 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____21421, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____21438 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____21438, mname, decls, false)
           in
        match uu____21385 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____21468 = desugar_decls env2 decls  in
            (match uu____21468 with
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
          let uu____21522 =
            (FStar_Options.interactive ()) &&
              (let uu____21524 =
                 let uu____21525 =
                   let uu____21526 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____21526  in
                 FStar_Util.get_file_extension uu____21525  in
               FStar_List.mem uu____21524 ["fsti"; "fsi"])
             in
          if uu____21522 then as_interface m else m  in
        let uu____21530 = desugar_modul_common curmod env m1  in
        match uu____21530 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____21545 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____21561 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____21561 with
      | (env1,modul,pop_when_done) ->
          let uu____21575 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____21575 with
           | (env2,modul1) ->
               ((let uu____21587 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____21587
                 then
                   let uu____21588 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____21588
                 else ());
                (let uu____21590 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____21590, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____21604 = desugar_modul env modul  in
      match uu____21604 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____21631 = desugar_decls env decls  in
      match uu____21631 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____21669 = desugar_partial_modul modul env a_modul  in
        match uu____21669 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____21743 ->
                  let t =
                    let uu____21751 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____21751  in
                  let uu____21760 =
                    let uu____21761 = FStar_Syntax_Subst.compress t  in
                    uu____21761.FStar_Syntax_Syntax.n  in
                  (match uu____21760 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____21771,uu____21772)
                       -> bs1
                   | uu____21793 -> failwith "Impossible")
               in
            let uu____21800 =
              let uu____21807 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____21807
                FStar_Syntax_Syntax.t_unit
               in
            match uu____21800 with
            | (binders,uu____21809,binders_opening) ->
                let erase_term t =
                  let uu____21815 =
                    let uu____21816 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____21816  in
                  FStar_Syntax_Subst.close binders uu____21815  in
                let erase_tscheme uu____21832 =
                  match uu____21832 with
                  | (us,t) ->
                      let t1 =
                        let uu____21852 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____21852 t  in
                      let uu____21855 =
                        let uu____21856 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____21856  in
                      ([], uu____21855)
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
                    | uu____21885 ->
                        let bs =
                          let uu____21893 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____21893  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____21923 =
                          let uu____21924 =
                            let uu____21927 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____21927  in
                          uu____21924.FStar_Syntax_Syntax.n  in
                        (match uu____21923 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____21935,uu____21936) -> bs1
                         | uu____21957 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____21968 =
                      let uu____21969 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____21969  in
                    FStar_Syntax_Subst.close binders uu____21968  in
                  let uu___142_21970 = action  in
                  let uu____21971 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____21972 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___142_21970.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___142_21970.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____21971;
                    FStar_Syntax_Syntax.action_typ = uu____21972
                  }  in
                let uu___143_21973 = ed  in
                let uu____21974 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____21975 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____21976 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____21977 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____21978 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____21979 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____21980 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____21981 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____21982 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____21983 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____21984 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____21985 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____21986 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____21987 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____21988 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____21989 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___143_21973.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___143_21973.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____21974;
                  FStar_Syntax_Syntax.signature = uu____21975;
                  FStar_Syntax_Syntax.ret_wp = uu____21976;
                  FStar_Syntax_Syntax.bind_wp = uu____21977;
                  FStar_Syntax_Syntax.if_then_else = uu____21978;
                  FStar_Syntax_Syntax.ite_wp = uu____21979;
                  FStar_Syntax_Syntax.stronger = uu____21980;
                  FStar_Syntax_Syntax.close_wp = uu____21981;
                  FStar_Syntax_Syntax.assert_p = uu____21982;
                  FStar_Syntax_Syntax.assume_p = uu____21983;
                  FStar_Syntax_Syntax.null_wp = uu____21984;
                  FStar_Syntax_Syntax.trivial = uu____21985;
                  FStar_Syntax_Syntax.repr = uu____21986;
                  FStar_Syntax_Syntax.return_repr = uu____21987;
                  FStar_Syntax_Syntax.bind_repr = uu____21988;
                  FStar_Syntax_Syntax.actions = uu____21989;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___143_21973.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___144_22001 = se  in
                  let uu____22002 =
                    let uu____22003 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____22003  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____22002;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___144_22001.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___144_22001.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___144_22001.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___144_22001.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___145_22007 = se  in
                  let uu____22008 =
                    let uu____22009 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22009
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____22008;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___145_22007.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___145_22007.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___145_22007.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___145_22007.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____22011 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____22012 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____22012 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____22024 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____22024
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____22026 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____22026)
  