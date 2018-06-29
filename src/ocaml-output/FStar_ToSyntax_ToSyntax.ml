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
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___233_74  ->
        match uu___233_74 with
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
  fun uu___234_83  ->
    match uu___234_83 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___235_94  ->
    match uu___235_94 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____97 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____104 .
    FStar_Parser_AST.imp ->
      'Auu____104 ->
        ('Auu____104,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____129 .
    FStar_Parser_AST.imp ->
      'Auu____129 ->
        ('Auu____129,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____148 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____165 -> true
            | uu____170 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____177 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____183 =
      let uu____184 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____184  in
    FStar_Parser_AST.mk_term uu____183 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____190 =
      let uu____191 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____191  in
    FStar_Parser_AST.mk_term uu____190 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____202 =
        let uu____203 = unparen t  in uu____203.FStar_Parser_AST.tm  in
      match uu____202 with
      | FStar_Parser_AST.Name l ->
          let uu____205 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____205 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____211) ->
          let uu____224 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____224 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____230,uu____231) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____234,uu____235) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____240,t1) -> is_comp_type env t1
      | uu____242 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____258 =
          let uu____261 =
            let uu____262 =
              let uu____267 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____267, r)  in
            FStar_Ident.mk_ident uu____262  in
          [uu____261]  in
        FStar_All.pipe_right uu____258 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____280 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____280 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____316 =
              let uu____317 =
                let uu____318 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____318 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____317 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____316  in
          let fallback uu____326 =
            let uu____327 = FStar_Ident.text_of_id op  in
            match uu____327 with
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
                let uu____330 = FStar_Options.ml_ish ()  in
                if uu____330
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
            | uu____334 -> FStar_Pervasives_Native.None  in
          let uu____335 =
            let uu____342 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____342  in
          match uu____335 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____354 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____372 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____372
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____419 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____423 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____423 with | (env1,uu____435) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____438,term) ->
          let uu____440 = free_type_vars env term  in (env, uu____440)
      | FStar_Parser_AST.TAnnotated (id1,uu____446) ->
          let uu____447 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____447 with | (env1,uu____459) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____463 = free_type_vars env t  in (env, uu____463)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____470 =
        let uu____471 = unparen t  in uu____471.FStar_Parser_AST.tm  in
      match uu____470 with
      | FStar_Parser_AST.Labeled uu____474 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____484 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____484 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____497 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____504 -> []
      | FStar_Parser_AST.Uvar uu____505 -> []
      | FStar_Parser_AST.Var uu____506 -> []
      | FStar_Parser_AST.Projector uu____507 -> []
      | FStar_Parser_AST.Discrim uu____512 -> []
      | FStar_Parser_AST.Name uu____513 -> []
      | FStar_Parser_AST.Requires (t1,uu____515) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____521) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____526,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____544,ts) ->
          FStar_List.collect
            (fun uu____565  ->
               match uu____565 with | (t1,uu____573) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____574,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____582) ->
          let uu____583 = free_type_vars env t1  in
          let uu____586 = free_type_vars env t2  in
          FStar_List.append uu____583 uu____586
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____591 = free_type_vars_b env b  in
          (match uu____591 with
           | (env1,f) ->
               let uu____606 = free_type_vars env1 t1  in
               FStar_List.append f uu____606)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____615 =
            FStar_List.fold_left
              (fun uu____635  ->
                 fun binder  ->
                   match uu____635 with
                   | (env1,free) ->
                       let uu____655 = free_type_vars_b env1 binder  in
                       (match uu____655 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____615 with
           | (env1,free) ->
               let uu____686 = free_type_vars env1 body  in
               FStar_List.append free uu____686)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____695 =
            FStar_List.fold_left
              (fun uu____715  ->
                 fun binder  ->
                   match uu____715 with
                   | (env1,free) ->
                       let uu____735 = free_type_vars_b env1 binder  in
                       (match uu____735 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____695 with
           | (env1,free) ->
               let uu____766 = free_type_vars env1 body  in
               FStar_List.append free uu____766)
      | FStar_Parser_AST.Project (t1,uu____770) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____774 -> []
      | FStar_Parser_AST.Let uu____781 -> []
      | FStar_Parser_AST.LetOpen uu____802 -> []
      | FStar_Parser_AST.If uu____807 -> []
      | FStar_Parser_AST.QForall uu____814 -> []
      | FStar_Parser_AST.QExists uu____827 -> []
      | FStar_Parser_AST.Record uu____840 -> []
      | FStar_Parser_AST.Match uu____853 -> []
      | FStar_Parser_AST.TryWith uu____868 -> []
      | FStar_Parser_AST.Bind uu____883 -> []
      | FStar_Parser_AST.Quote uu____890 -> []
      | FStar_Parser_AST.VQuote uu____895 -> []
      | FStar_Parser_AST.Antiquote uu____896 -> []
      | FStar_Parser_AST.Seq uu____901 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____954 =
        let uu____955 = unparen t1  in uu____955.FStar_Parser_AST.tm  in
      match uu____954 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____997 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1021 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1021  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1039 =
                     let uu____1040 =
                       let uu____1045 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1045)  in
                     FStar_Parser_AST.TAnnotated uu____1040  in
                   FStar_Parser_AST.mk_binder uu____1039
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
        let uu____1062 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1062  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1080 =
                     let uu____1081 =
                       let uu____1086 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1086)  in
                     FStar_Parser_AST.TAnnotated uu____1081  in
                   FStar_Parser_AST.mk_binder uu____1080
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1088 =
             let uu____1089 = unparen t  in uu____1089.FStar_Parser_AST.tm
              in
           match uu____1088 with
           | FStar_Parser_AST.Product uu____1090 -> t
           | uu____1097 ->
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
      | uu____1133 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1141,uu____1142) -> true
    | FStar_Parser_AST.PatVar (uu____1147,uu____1148) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1154) -> is_var_pattern p1
    | uu____1167 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1174) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1187;
           FStar_Parser_AST.prange = uu____1188;_},uu____1189)
        -> true
    | uu____1200 -> false
  
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
    | uu____1214 -> p
  
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
            let uu____1284 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1284 with
             | (name,args,uu____1327) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1377);
               FStar_Parser_AST.prange = uu____1378;_},args)
            when is_top_level1 ->
            let uu____1388 =
              let uu____1393 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1393  in
            (uu____1388, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1415);
               FStar_Parser_AST.prange = uu____1416;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1446 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1496 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1497,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1500 -> acc
      | FStar_Parser_AST.PatTvar uu____1501 -> acc
      | FStar_Parser_AST.PatOp uu____1508 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1516) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1525) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1540 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1540
      | FStar_Parser_AST.PatAscribed (pat,uu____1548) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1610 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1646 -> false
  
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
  fun uu___236_1692  ->
    match uu___236_1692 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1699 -> failwith "Impossible"
  
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
  fun uu____1732  ->
    match uu____1732 with
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
      let uu____1812 =
        let uu____1829 =
          let uu____1832 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1832  in
        let uu____1833 =
          let uu____1844 =
            let uu____1853 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1853)  in
          [uu____1844]  in
        (uu____1829, uu____1833)  in
      FStar_Syntax_Syntax.Tm_app uu____1812  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1900 =
        let uu____1917 =
          let uu____1920 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1920  in
        let uu____1921 =
          let uu____1932 =
            let uu____1941 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1941)  in
          [uu____1932]  in
        (uu____1917, uu____1921)  in
      FStar_Syntax_Syntax.Tm_app uu____1900  in
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
          let uu____2002 =
            let uu____2019 =
              let uu____2022 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2022  in
            let uu____2023 =
              let uu____2034 =
                let uu____2043 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2043)  in
              let uu____2050 =
                let uu____2061 =
                  let uu____2070 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2070)  in
                [uu____2061]  in
              uu____2034 :: uu____2050  in
            (uu____2019, uu____2023)  in
          FStar_Syntax_Syntax.Tm_app uu____2002  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2128 =
        let uu____2143 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2162  ->
               match uu____2162 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2173;
                    FStar_Syntax_Syntax.index = uu____2174;
                    FStar_Syntax_Syntax.sort = t;_},uu____2176)
                   ->
                   let uu____2183 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2183) uu____2143
         in
      FStar_All.pipe_right bs uu____2128  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2199 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2216 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2242 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2263,uu____2264,bs,t,uu____2267,uu____2268)
                            ->
                            let uu____2277 = bs_univnames bs  in
                            let uu____2280 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2277 uu____2280
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2283,uu____2284,t,uu____2286,uu____2287,uu____2288)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2293 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2242 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___262_2301 = s  in
        let uu____2302 =
          let uu____2303 =
            let uu____2312 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2330,bs,t,lids1,lids2) ->
                          let uu___263_2343 = se  in
                          let uu____2344 =
                            let uu____2345 =
                              let uu____2362 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2363 =
                                let uu____2364 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2364 t  in
                              (lid, uvs, uu____2362, uu____2363, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2345
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2344;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___263_2343.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___263_2343.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___263_2343.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___263_2343.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2378,t,tlid,n1,lids1) ->
                          let uu___264_2387 = se  in
                          let uu____2388 =
                            let uu____2389 =
                              let uu____2404 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2404, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2389  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2388;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___264_2387.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___264_2387.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___264_2387.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___264_2387.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2407 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2312, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2303  in
        {
          FStar_Syntax_Syntax.sigel = uu____2302;
          FStar_Syntax_Syntax.sigrng =
            (uu___262_2301.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___262_2301.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___262_2301.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___262_2301.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2413,t) ->
        let uvs =
          let uu____2416 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2416 FStar_Util.set_elements  in
        let uu___265_2421 = s  in
        let uu____2422 =
          let uu____2423 =
            let uu____2430 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2430)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2423  in
        {
          FStar_Syntax_Syntax.sigel = uu____2422;
          FStar_Syntax_Syntax.sigrng =
            (uu___265_2421.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___265_2421.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___265_2421.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___265_2421.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2452 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2455 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2462) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2495,(FStar_Util.Inl t,uu____2497),uu____2498)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2545,(FStar_Util.Inr c,uu____2547),uu____2548)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2595 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2596,(FStar_Util.Inl t,uu____2598),uu____2599) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2646,(FStar_Util.Inr c,uu____2648),uu____2649) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2696 -> empty_set  in
          FStar_Util.set_union uu____2452 uu____2455  in
        let all_lb_univs =
          let uu____2700 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2716 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2716) empty_set)
             in
          FStar_All.pipe_right uu____2700 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___266_2726 = s  in
        let uu____2727 =
          let uu____2728 =
            let uu____2735 =
              let uu____2736 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___267_2748 = lb  in
                        let uu____2749 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2752 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___267_2748.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2749;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___267_2748.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2752;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___267_2748.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___267_2748.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2736)  in
            (uu____2735, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2728  in
        {
          FStar_Syntax_Syntax.sigel = uu____2727;
          FStar_Syntax_Syntax.sigrng =
            (uu___266_2726.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___266_2726.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___266_2726.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___266_2726.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2760,fml) ->
        let uvs =
          let uu____2763 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2763 FStar_Util.set_elements  in
        let uu___268_2768 = s  in
        let uu____2769 =
          let uu____2770 =
            let uu____2777 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2777)  in
          FStar_Syntax_Syntax.Sig_assume uu____2770  in
        {
          FStar_Syntax_Syntax.sigel = uu____2769;
          FStar_Syntax_Syntax.sigrng =
            (uu___268_2768.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___268_2768.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___268_2768.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___268_2768.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2779,bs,c,flags1) ->
        let uvs =
          let uu____2788 =
            let uu____2791 = bs_univnames bs  in
            let uu____2794 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2791 uu____2794  in
          FStar_All.pipe_right uu____2788 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___269_2802 = s  in
        let uu____2803 =
          let uu____2804 =
            let uu____2817 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____2818 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2817, uu____2818, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2804  in
        {
          FStar_Syntax_Syntax.sigel = uu____2803;
          FStar_Syntax_Syntax.sigrng =
            (uu___269_2802.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___269_2802.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___269_2802.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___269_2802.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____2821 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___237_2826  ->
    match uu___237_2826 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2827 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2839 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2839)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2858 =
      let uu____2859 = unparen t  in uu____2859.FStar_Parser_AST.tm  in
    match uu____2858 with
    | FStar_Parser_AST.Wild  ->
        let uu____2864 =
          let uu____2865 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2865  in
        FStar_Util.Inr uu____2864
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2876)) ->
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
             let uu____2941 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2941
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2952 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2952
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2963 =
               let uu____2968 =
                 let uu____2969 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2969
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2968)
                in
             FStar_Errors.raise_error uu____2963 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2974 ->
        let rec aux t1 univargs =
          let uu____3008 =
            let uu____3009 = unparen t1  in uu____3009.FStar_Parser_AST.tm
             in
          match uu____3008 with
          | FStar_Parser_AST.App (t2,targ,uu____3016) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___238_3039  ->
                     match uu___238_3039 with
                     | FStar_Util.Inr uu____3044 -> true
                     | uu____3045 -> false) univargs
              then
                let uu____3050 =
                  let uu____3051 =
                    FStar_List.map
                      (fun uu___239_3060  ->
                         match uu___239_3060 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3051  in
                FStar_Util.Inr uu____3050
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___240_3077  ->
                        match uu___240_3077 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3083 -> failwith "impossible")
                     univargs
                    in
                 let uu____3084 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3084)
          | uu____3090 ->
              let uu____3091 =
                let uu____3096 =
                  let uu____3097 =
                    let uu____3098 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3098 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3097  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3096)  in
              FStar_Errors.raise_error uu____3091 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3107 ->
        let uu____3108 =
          let uu____3113 =
            let uu____3114 =
              let uu____3115 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3115 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3114  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3113)  in
        FStar_Errors.raise_error uu____3108 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____3148 ->
        let uu____3171 =
          let uu____3176 =
            let uu____3177 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____3177
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3176)  in
        FStar_Errors.raise_error uu____3171 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3187 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3187) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3215 = FStar_List.hd fields  in
        match uu____3215 with
        | (f,uu____3225) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3237 =
                match uu____3237 with
                | (f',uu____3243) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3245 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3245
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
              (let uu____3249 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3249);
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
              FStar_All.pipe_right uu____3745 (fun a236  -> ())
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
                           let uu___270_4066 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___271_4071 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___271_4071.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___271_4071.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___270_4066.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___272_4073 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___273_4078 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___273_4078.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___273_4078.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___272_4073.FStar_Syntax_Syntax.p)
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
                                  ((let uu___274_4135 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___274_4135.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___274_4135.FStar_Syntax_Syntax.index);
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
               let aq1 = trans_aqual env1 aq  in
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
               let aq1 = trans_aqual env1 aq  in
               let uu____4222 = resolvex loc env1 x  in
               (match uu____4222 with
                | (loc1,env2,xbv) ->
                    let uu____4244 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4244, imp))
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
               let uu____4254 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4254, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____4276;_},args)
               ->
               let uu____4282 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____4323  ->
                        match uu____4323 with
                        | (loc1,env2,args1) ->
                            let uu____4371 = aux loc1 env2 arg  in
                            (match uu____4371 with
                             | (loc2,env3,uu____4400,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____4282 with
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
                    let uu____4470 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____4470, false))
           | FStar_Parser_AST.PatApp uu____4485 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____4507 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____4540  ->
                        match uu____4540 with
                        | (loc1,env2,pats1) ->
                            let uu____4572 = aux loc1 env2 pat  in
                            (match uu____4572 with
                             | (loc2,env3,uu____4597,pat1,uu____4599) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____4507 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____4642 =
                        let uu____4645 =
                          let uu____4652 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____4652  in
                        let uu____4653 =
                          let uu____4654 =
                            let uu____4667 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____4667, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____4654  in
                        FStar_All.pipe_left uu____4645 uu____4653  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____4699 =
                               let uu____4700 =
                                 let uu____4713 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____4713, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____4700  in
                             FStar_All.pipe_left (pos_r r) uu____4699) pats1
                        uu____4642
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
               let uu____4755 =
                 FStar_List.fold_left
                   (fun uu____4795  ->
                      fun p2  ->
                        match uu____4795 with
                        | (loc1,env2,pats) ->
                            let uu____4844 = aux loc1 env2 p2  in
                            (match uu____4844 with
                             | (loc2,env3,uu____4873,pat,uu____4875) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4755 with
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
                    let uu____4970 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____4970 with
                     | (constr,uu____4992) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____4995 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____4997 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____4997, false)))
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
                      (fun uu____5066  ->
                         match uu____5066 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____5096  ->
                         match uu____5096 with
                         | (f,uu____5102) ->
                             let uu____5103 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____5129  ->
                                       match uu____5129 with
                                       | (g,uu____5135) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____5103 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____5140,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____5147 =
                   let uu____5148 =
                     let uu____5155 =
                       let uu____5156 =
                         let uu____5157 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____5157  in
                       FStar_Parser_AST.mk_pattern uu____5156
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____5155, args)  in
                   FStar_Parser_AST.PatApp uu____5148  in
                 FStar_Parser_AST.mk_pattern uu____5147
                   p1.FStar_Parser_AST.prange
                  in
               let uu____5160 = aux loc env1 app  in
               (match uu____5160 with
                | (env2,e,b,p2,uu____5189) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____5217 =
                            let uu____5218 =
                              let uu____5231 =
                                let uu___275_5232 = fv  in
                                let uu____5233 =
                                  let uu____5236 =
                                    let uu____5237 =
                                      let uu____5244 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____5244)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____5237
                                     in
                                  FStar_Pervasives_Native.Some uu____5236  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___275_5232.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___275_5232.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____5233
                                }  in
                              (uu____5231, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____5218  in
                          FStar_All.pipe_left pos uu____5217
                      | uu____5271 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____5325 = aux' true loc env1 p2  in
               (match uu____5325 with
                | (loc1,env2,var,p3,uu____5352) ->
                    let uu____5357 =
                      FStar_List.fold_left
                        (fun uu____5389  ->
                           fun p4  ->
                             match uu____5389 with
                             | (loc2,env3,ps1) ->
                                 let uu____5422 = aux' true loc2 env3 p4  in
                                 (match uu____5422 with
                                  | (loc3,env4,uu____5447,p5,uu____5449) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____5357 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____5500 ->
               let uu____5501 = aux' true loc env1 p1  in
               (match uu____5501 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____5541 = aux_maybe_or env p  in
         match uu____5541 with
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
            let uu____5600 =
              let uu____5601 =
                let uu____5612 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____5612,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____5601  in
            (env, uu____5600, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____5640 =
                  let uu____5641 =
                    let uu____5646 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____5646, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____5641  in
                mklet uu____5640
            | FStar_Parser_AST.PatVar (x,uu____5648) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____5654);
                   FStar_Parser_AST.prange = uu____5655;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____5675 =
                  let uu____5676 =
                    let uu____5687 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____5688 =
                      let uu____5695 = desugar_term env t  in
                      (uu____5695, tacopt1)  in
                    (uu____5687, uu____5688)  in
                  LetBinder uu____5676  in
                (env, uu____5675, [])
            | uu____5706 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5716 = desugar_data_pat env p is_mut  in
             match uu____5716 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5745;
                       FStar_Syntax_Syntax.p = uu____5746;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5747;
                       FStar_Syntax_Syntax.p = uu____5748;_}::[] -> []
                   | uu____5749 -> p1  in
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
  fun uu____5756  ->
    fun env  ->
      fun pat  ->
        let uu____5759 = desugar_data_pat env pat false  in
        match uu____5759 with | (env1,uu____5775,pat1) -> (env1, pat1)

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
      let uu____5794 = desugar_term_aq env e  in
      match uu____5794 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____5811 = desugar_typ_aq env e  in
      match uu____5811 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5821  ->
        fun range  ->
          match uu____5821 with
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
              ((let uu____5831 =
                  let uu____5832 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5832  in
                if uu____5831
                then
                  let uu____5833 =
                    let uu____5838 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5838)  in
                  FStar_Errors.log_issue range uu____5833
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
                  let uu____5843 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____5843 range  in
                let lid1 =
                  let uu____5847 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____5847 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____5857) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5866 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____5866 range  in
                           let private_fv =
                             let uu____5868 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5868 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___276_5869 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___276_5869.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___276_5869.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5870 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5877 =
                        let uu____5882 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5882)
                         in
                      FStar_Errors.raise_error uu____5877 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____5898 =
                  let uu____5905 =
                    let uu____5906 =
                      let uu____5923 =
                        let uu____5934 =
                          let uu____5943 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____5943)  in
                        [uu____5934]  in
                      (lid1, uu____5923)  in
                    FStar_Syntax_Syntax.Tm_app uu____5906  in
                  FStar_Syntax_Syntax.mk uu____5905  in
                uu____5898 FStar_Pervasives_Native.None range))

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
            let uu____5992 =
              let uu____6001 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____6001 l  in
            match uu____5992 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____6056;
                              FStar_Syntax_Syntax.vars = uu____6057;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6084 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6084 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____6094 =
                                 let uu____6095 =
                                   let uu____6098 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____6098  in
                                 uu____6095.FStar_Syntax_Syntax.n  in
                               match uu____6094 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____6120))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____6121 -> msg
                             else msg  in
                           let uu____6123 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6123
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6126 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6126 " is deprecated"  in
                           let uu____6127 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6127
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____6128 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____6133 =
                      let uu____6134 =
                        let uu____6141 = mk_ref_read tm1  in
                        (uu____6141,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____6134  in
                    FStar_All.pipe_left mk1 uu____6133
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____6159 =
          let uu____6160 = unparen t  in uu____6160.FStar_Parser_AST.tm  in
        match uu____6159 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____6161; FStar_Ident.ident = uu____6162;
              FStar_Ident.nsstr = uu____6163; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____6166 ->
            let uu____6167 =
              let uu____6172 =
                let uu____6173 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____6173  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____6172)  in
            FStar_Errors.raise_error uu____6167 t.FStar_Parser_AST.range
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
          let uu___277_6268 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___277_6268.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___277_6268.FStar_Syntax_Syntax.vars)
          }  in
        let uu____6271 =
          let uu____6272 = unparen top  in uu____6272.FStar_Parser_AST.tm  in
        match uu____6271 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____6277 ->
            let uu____6284 = desugar_formula env top  in (uu____6284, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____6291 = desugar_formula env t  in (uu____6291, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____6298 = desugar_formula env t  in (uu____6298, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____6322 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____6322, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____6324 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____6324, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____6332 =
                let uu____6333 =
                  let uu____6340 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____6340, args)  in
                FStar_Parser_AST.Op uu____6333  in
              FStar_Parser_AST.mk_term uu____6332 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____6343 =
              let uu____6344 =
                let uu____6345 =
                  let uu____6352 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____6352, [e])  in
                FStar_Parser_AST.Op uu____6345  in
              FStar_Parser_AST.mk_term uu____6344 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____6343
        | FStar_Parser_AST.Op (op_star,uu____6356::uu____6357::[]) when
            (let uu____6362 = FStar_Ident.text_of_id op_star  in
             uu____6362 = "*") &&
              (let uu____6364 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____6364 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____6379;_},t1::t2::[])
                  ->
                  let uu____6384 = flatten1 t1  in
                  FStar_List.append uu____6384 [t2]
              | uu____6387 -> [t]  in
            let uu____6388 =
              let uu____6415 =
                let uu____6440 =
                  let uu____6443 = unparen top  in flatten1 uu____6443  in
                FStar_All.pipe_right uu____6440
                  (FStar_List.map
                     (fun t  ->
                        let uu____6480 = desugar_typ_aq env t  in
                        match uu____6480 with
                        | (t',aq) ->
                            let uu____6491 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____6491, aq)))
                 in
              FStar_All.pipe_right uu____6415 FStar_List.unzip  in
            (match uu____6388 with
             | (targs,aqs) ->
                 let uu____6610 =
                   let uu____6615 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____6615
                    in
                 (match uu____6610 with
                  | (tup,uu____6633) ->
                      let uu____6634 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____6634, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____6648 =
              let uu____6649 =
                let uu____6652 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____6652  in
              FStar_All.pipe_left setpos uu____6649  in
            (uu____6648, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____6664 =
              let uu____6669 =
                let uu____6670 =
                  let uu____6671 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____6671 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____6670  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____6669)  in
            FStar_Errors.raise_error uu____6664 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____6682 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____6682 with
             | FStar_Pervasives_Native.None  ->
                 let uu____6689 =
                   let uu____6694 =
                     let uu____6695 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____6695
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____6694)
                    in
                 FStar_Errors.raise_error uu____6689
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____6705 =
                     let uu____6732 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____6798 = desugar_term_aq env t  in
                               match uu____6798 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____6732 FStar_List.unzip  in
                   (match uu____6705 with
                    | (args1,aqs) ->
                        let uu____6941 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6941, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6957)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6972 =
              let uu___278_6973 = top  in
              let uu____6974 =
                let uu____6975 =
                  let uu____6982 =
                    let uu___279_6983 = top  in
                    let uu____6984 =
                      let uu____6985 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6985  in
                    {
                      FStar_Parser_AST.tm = uu____6984;
                      FStar_Parser_AST.range =
                        (uu___279_6983.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___279_6983.FStar_Parser_AST.level)
                    }  in
                  (uu____6982, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6975  in
              {
                FStar_Parser_AST.tm = uu____6974;
                FStar_Parser_AST.range =
                  (uu___278_6973.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___278_6973.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6972
        | FStar_Parser_AST.Construct (n1,(a,uu____6988)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____7004 =
                let uu___280_7005 = top  in
                let uu____7006 =
                  let uu____7007 =
                    let uu____7014 =
                      let uu___281_7015 = top  in
                      let uu____7016 =
                        let uu____7017 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____7017  in
                      {
                        FStar_Parser_AST.tm = uu____7016;
                        FStar_Parser_AST.range =
                          (uu___281_7015.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___281_7015.FStar_Parser_AST.level)
                      }  in
                    (uu____7014, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____7007  in
                {
                  FStar_Parser_AST.tm = uu____7006;
                  FStar_Parser_AST.range =
                    (uu___280_7005.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___280_7005.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____7004))
        | FStar_Parser_AST.Construct (n1,(a,uu____7020)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____7035 =
              let uu___282_7036 = top  in
              let uu____7037 =
                let uu____7038 =
                  let uu____7045 =
                    let uu___283_7046 = top  in
                    let uu____7047 =
                      let uu____7048 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____7048  in
                    {
                      FStar_Parser_AST.tm = uu____7047;
                      FStar_Parser_AST.range =
                        (uu___283_7046.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___283_7046.FStar_Parser_AST.level)
                    }  in
                  (uu____7045, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____7038  in
              {
                FStar_Parser_AST.tm = uu____7037;
                FStar_Parser_AST.range =
                  (uu___282_7036.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___282_7036.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____7035
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7049; FStar_Ident.ident = uu____7050;
              FStar_Ident.nsstr = uu____7051; FStar_Ident.str = "Type0";_}
            ->
            let uu____7054 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____7054, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7055; FStar_Ident.ident = uu____7056;
              FStar_Ident.nsstr = uu____7057; FStar_Ident.str = "Type";_}
            ->
            let uu____7060 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____7060, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____7061; FStar_Ident.ident = uu____7062;
               FStar_Ident.nsstr = uu____7063; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____7081 =
              let uu____7082 =
                let uu____7083 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____7083  in
              mk1 uu____7082  in
            (uu____7081, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7084; FStar_Ident.ident = uu____7085;
              FStar_Ident.nsstr = uu____7086; FStar_Ident.str = "Effect";_}
            ->
            let uu____7089 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____7089, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7090; FStar_Ident.ident = uu____7091;
              FStar_Ident.nsstr = uu____7092; FStar_Ident.str = "True";_}
            ->
            let uu____7095 =
              let uu____7096 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7096
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7095, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7097; FStar_Ident.ident = uu____7098;
              FStar_Ident.nsstr = uu____7099; FStar_Ident.str = "False";_}
            ->
            let uu____7102 =
              let uu____7103 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7103
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7102, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____7106;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____7108 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____7108 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____7117 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____7117, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____7118 =
                    let uu____7119 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____7119 txt
                     in
                  failwith uu____7118))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7126 = desugar_name mk1 setpos env true l  in
              (uu____7126, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7129 = desugar_name mk1 setpos env true l  in
              (uu____7129, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____7140 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____7140 with
                | FStar_Pervasives_Native.Some uu____7149 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____7154 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____7154 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____7168 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____7185 =
                    let uu____7186 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____7186  in
                  (uu____7185, noaqs)
              | uu____7187 ->
                  let uu____7194 =
                    let uu____7199 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____7199)  in
                  FStar_Errors.raise_error uu____7194
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____7206 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____7206 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7213 =
                    let uu____7218 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____7218)
                     in
                  FStar_Errors.raise_error uu____7213
                    top.FStar_Parser_AST.range
              | uu____7223 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____7227 = desugar_name mk1 setpos env true lid'  in
                  (uu____7227, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7243 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____7243 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____7262 ->
                       let uu____7269 =
                         FStar_Util.take
                           (fun uu____7293  ->
                              match uu____7293 with
                              | (uu____7298,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____7269 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____7343 =
                              let uu____7370 =
                                FStar_List.map
                                  (fun uu____7415  ->
                                     match uu____7415 with
                                     | (t,imp) ->
                                         let uu____7432 =
                                           desugar_term_aq env t  in
                                         (match uu____7432 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____7370
                                FStar_List.unzip
                               in
                            (match uu____7343 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____7583 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____7583, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____7601 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____7601 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____7608 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____7619 =
              FStar_List.fold_left
                (fun uu____7664  ->
                   fun b  ->
                     match uu____7664 with
                     | (env1,tparams,typs) ->
                         let uu____7721 = desugar_binder env1 b  in
                         (match uu____7721 with
                          | (xopt,t1) ->
                              let uu____7750 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____7759 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____7759)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____7750 with
                               | (env2,x) ->
                                   let uu____7779 =
                                     let uu____7782 =
                                       let uu____7785 =
                                         let uu____7786 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7786
                                          in
                                       [uu____7785]  in
                                     FStar_List.append typs uu____7782  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___284_7812 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___284_7812.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___284_7812.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____7779)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____7619 with
             | (env1,uu____7840,targs) ->
                 let uu____7862 =
                   let uu____7867 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7867
                    in
                 (match uu____7862 with
                  | (tup,uu____7877) ->
                      let uu____7878 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7878, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7897 = uncurry binders t  in
            (match uu____7897 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___241_7941 =
                   match uu___241_7941 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7957 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7957
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7981 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7981 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____8014 = aux env [] bs  in (uu____8014, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____8023 = desugar_binder env b  in
            (match uu____8023 with
             | (FStar_Pervasives_Native.None ,uu____8034) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____8048 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____8048 with
                  | ((x,uu____8064),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____8077 =
                        let uu____8078 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____8078  in
                      (uu____8077, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____8096 =
              FStar_List.fold_left
                (fun uu____8116  ->
                   fun pat  ->
                     match uu____8116 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____8142,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____8152 =
                                let uu____8155 = free_type_vars env1 t  in
                                FStar_List.append uu____8155 ftvs  in
                              (env1, uu____8152)
                          | FStar_Parser_AST.PatAscribed
                              (uu____8160,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____8171 =
                                let uu____8174 = free_type_vars env1 t  in
                                let uu____8177 =
                                  let uu____8180 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____8180 ftvs  in
                                FStar_List.append uu____8174 uu____8177  in
                              (env1, uu____8171)
                          | uu____8185 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____8096 with
             | (uu____8194,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____8206 =
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
                   FStar_List.append uu____8206 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___242_8263 =
                   match uu___242_8263 with
                   | [] ->
                       let uu____8290 = desugar_term_aq env1 body  in
                       (match uu____8290 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____8327 =
                                      let uu____8328 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____8328
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____8327 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____8397 =
                              let uu____8400 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____8400  in
                            (uu____8397, aq))
                   | p::rest ->
                       let uu____8415 = desugar_binding_pat env1 p  in
                       (match uu____8415 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____8451 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____8458 =
                              match b with
                              | LetBinder uu____8499 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____8567) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____8621 =
                                          let uu____8630 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____8630, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____8621
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____8692,uu____8693) ->
                                             let tup2 =
                                               let uu____8695 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8695
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8699 =
                                                 let uu____8706 =
                                                   let uu____8707 =
                                                     let uu____8724 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____8727 =
                                                       let uu____8738 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____8747 =
                                                         let uu____8758 =
                                                           let uu____8767 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____8767
                                                            in
                                                         [uu____8758]  in
                                                       uu____8738 ::
                                                         uu____8747
                                                        in
                                                     (uu____8724, uu____8727)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8707
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8706
                                                  in
                                               uu____8699
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____8818 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____8818
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____8861,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____8863,pats)) ->
                                             let tupn =
                                               let uu____8906 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8906
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8918 =
                                                 let uu____8919 =
                                                   let uu____8936 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____8939 =
                                                     let uu____8950 =
                                                       let uu____8961 =
                                                         let uu____8970 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____8970
                                                          in
                                                       [uu____8961]  in
                                                     FStar_List.append args
                                                       uu____8950
                                                      in
                                                   (uu____8936, uu____8939)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8919
                                                  in
                                               mk1 uu____8918  in
                                             let p2 =
                                               let uu____9018 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____9018
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____9059 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____8458 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____9152,uu____9153,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____9175 =
                let uu____9176 = unparen e  in uu____9176.FStar_Parser_AST.tm
                 in
              match uu____9175 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____9186 ->
                  let uu____9187 = desugar_term_aq env e  in
                  (match uu____9187 with
                   | (head1,aq) ->
                       let uu____9200 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____9200, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____9207 ->
            let rec aux args aqs e =
              let uu____9290 =
                let uu____9291 = unparen e  in uu____9291.FStar_Parser_AST.tm
                 in
              match uu____9290 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____9311 = desugar_term_aq env t  in
                  (match uu____9311 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____9363 ->
                  let uu____9364 = desugar_term_aq env e  in
                  (match uu____9364 with
                   | (head1,aq) ->
                       let uu____9387 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____9387, (join_aqs (aq :: aqs))))
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
            let uu____9453 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____9453
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
            let uu____9505 = desugar_term_aq env t  in
            (match uu____9505 with
             | (tm,s) ->
                 let uu____9516 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____9516, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____9522 =
              let uu____9535 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____9535 then desugar_typ_aq else desugar_term_aq  in
            uu____9522 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____9590 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____9733  ->
                        match uu____9733 with
                        | (attr_opt,(p,def)) ->
                            let uu____9791 = is_app_pattern p  in
                            if uu____9791
                            then
                              let uu____9822 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____9822, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____9904 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____9904, def1)
                               | uu____9949 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____9987);
                                           FStar_Parser_AST.prange =
                                             uu____9988;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____10036 =
                                            let uu____10057 =
                                              let uu____10062 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____10062  in
                                            (uu____10057, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____10036, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____10153) ->
                                        if top_level
                                        then
                                          let uu____10188 =
                                            let uu____10209 =
                                              let uu____10214 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____10214  in
                                            (uu____10209, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____10188, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____10304 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____10335 =
                FStar_List.fold_left
                  (fun uu____10408  ->
                     fun uu____10409  ->
                       match (uu____10408, uu____10409) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____10517,uu____10518),uu____10519))
                           ->
                           let uu____10636 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____10662 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____10662 with
                                  | (env2,xx) ->
                                      let uu____10681 =
                                        let uu____10684 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____10684 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____10681))
                             | FStar_Util.Inr l ->
                                 let uu____10692 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____10692, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____10636 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____10335 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____10840 =
                    match uu____10840 with
                    | (attrs_opt,(uu____10876,args,result_t),def) ->
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
                                let uu____10964 = is_comp_type env1 t  in
                                if uu____10964
                                then
                                  ((let uu____10966 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____10976 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____10976))
                                       in
                                    match uu____10966 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____10979 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____10981 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____10981))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____10979
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
                          | uu____10988 ->
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
                              let uu____11003 =
                                let uu____11004 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____11004
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____11003
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
                  let uu____11081 = desugar_term_aq env' body  in
                  (match uu____11081 with
                   | (body1,aq) ->
                       let uu____11094 =
                         let uu____11097 =
                           let uu____11098 =
                             let uu____11111 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____11111)  in
                           FStar_Syntax_Syntax.Tm_let uu____11098  in
                         FStar_All.pipe_left mk1 uu____11097  in
                       (uu____11094, aq))
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
              let uu____11191 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____11191 with
              | (env1,binder,pat1) ->
                  let uu____11213 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____11239 = desugar_term_aq env1 t2  in
                        (match uu____11239 with
                         | (body1,aq) ->
                             let fv =
                               let uu____11253 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____11253
                                 FStar_Pervasives_Native.None
                                in
                             let uu____11254 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____11254, aq))
                    | LocalBinder (x,uu____11284) ->
                        let uu____11285 = desugar_term_aq env1 t2  in
                        (match uu____11285 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____11299;
                                   FStar_Syntax_Syntax.p = uu____11300;_}::[]
                                   -> body1
                               | uu____11301 ->
                                   let uu____11304 =
                                     let uu____11311 =
                                       let uu____11312 =
                                         let uu____11335 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____11338 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____11335, uu____11338)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11312
                                        in
                                     FStar_Syntax_Syntax.mk uu____11311  in
                                   uu____11304 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____11378 =
                               let uu____11381 =
                                 let uu____11382 =
                                   let uu____11395 =
                                     let uu____11398 =
                                       let uu____11399 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____11399]  in
                                     FStar_Syntax_Subst.close uu____11398
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____11395)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____11382  in
                               FStar_All.pipe_left mk1 uu____11381  in
                             (uu____11378, aq))
                     in
                  (match uu____11213 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____11462 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____11462, aq)
                       else (tm, aq))
               in
            let uu____11474 = FStar_List.hd lbs  in
            (match uu____11474 with
             | (attrs,(head_pat,defn)) ->
                 let uu____11518 = is_rec || (is_app_pattern head_pat)  in
                 if uu____11518
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____11531 =
                let uu____11532 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____11532  in
              mk1 uu____11531  in
            let uu____11533 = desugar_term_aq env t1  in
            (match uu____11533 with
             | (t1',aq1) ->
                 let uu____11544 = desugar_term_aq env t2  in
                 (match uu____11544 with
                  | (t2',aq2) ->
                      let uu____11555 = desugar_term_aq env t3  in
                      (match uu____11555 with
                       | (t3',aq3) ->
                           let uu____11566 =
                             let uu____11567 =
                               let uu____11568 =
                                 let uu____11591 =
                                   let uu____11608 =
                                     let uu____11623 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____11623,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____11636 =
                                     let uu____11653 =
                                       let uu____11668 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____11668,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____11653]  in
                                   uu____11608 :: uu____11636  in
                                 (t1', uu____11591)  in
                               FStar_Syntax_Syntax.Tm_match uu____11568  in
                             mk1 uu____11567  in
                           (uu____11566, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____11867 =
              match uu____11867 with
              | (pat,wopt,b) ->
                  let uu____11889 = desugar_match_pat env pat  in
                  (match uu____11889 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____11920 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____11920
                          in
                       let uu____11925 = desugar_term_aq env1 b  in
                       (match uu____11925 with
                        | (b1,aq) ->
                            let uu____11938 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____11938, aq)))
               in
            let uu____11943 = desugar_term_aq env e  in
            (match uu____11943 with
             | (e1,aq) ->
                 let uu____11954 =
                   let uu____11987 =
                     let uu____12022 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____12022 FStar_List.unzip  in
                   FStar_All.pipe_right uu____11987
                     (fun uu____12254  ->
                        match uu____12254 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____11954 with
                  | (brs,aqs) ->
                      let uu____12487 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____12487, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____12532 = is_comp_type env t  in
              if uu____12532
              then
                let uu____12541 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____12541
              else
                (let uu____12549 = desugar_term env t  in
                 FStar_Util.Inl uu____12549)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____12563 = desugar_term_aq env e  in
            (match uu____12563 with
             | (e1,aq) ->
                 let uu____12574 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____12574, aq))
        | FStar_Parser_AST.Record (uu____12607,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____12648 = FStar_List.hd fields  in
              match uu____12648 with | (f,uu____12660) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____12706  ->
                        match uu____12706 with
                        | (g,uu____12712) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____12718,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____12732 =
                         let uu____12737 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____12737)
                          in
                       FStar_Errors.raise_error uu____12732
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
                  let uu____12745 =
                    let uu____12756 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____12787  ->
                              match uu____12787 with
                              | (f,uu____12797) ->
                                  let uu____12798 =
                                    let uu____12799 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____12799
                                     in
                                  (uu____12798, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____12756)  in
                  FStar_Parser_AST.Construct uu____12745
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____12817 =
                      let uu____12818 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____12818  in
                    FStar_Parser_AST.mk_term uu____12817
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____12820 =
                      let uu____12833 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____12863  ->
                                match uu____12863 with
                                | (f,uu____12873) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____12833)  in
                    FStar_Parser_AST.Record uu____12820  in
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
            let uu____12933 = desugar_term_aq env recterm1  in
            (match uu____12933 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____12949;
                         FStar_Syntax_Syntax.vars = uu____12950;_},args)
                      ->
                      let uu____12976 =
                        let uu____12977 =
                          let uu____12978 =
                            let uu____12995 =
                              let uu____12998 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____12999 =
                                let uu____13002 =
                                  let uu____13003 =
                                    let uu____13010 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____13010)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____13003
                                   in
                                FStar_Pervasives_Native.Some uu____13002  in
                              FStar_Syntax_Syntax.fvar uu____12998
                                FStar_Syntax_Syntax.delta_constant
                                uu____12999
                               in
                            (uu____12995, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____12978  in
                        FStar_All.pipe_left mk1 uu____12977  in
                      (uu____12976, s)
                  | uu____13039 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____13043 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____13043 with
              | (constrname,is_rec) ->
                  let uu____13058 = desugar_term_aq env e  in
                  (match uu____13058 with
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
                       let uu____13076 =
                         let uu____13077 =
                           let uu____13078 =
                             let uu____13095 =
                               let uu____13098 =
                                 let uu____13099 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____13099
                                  in
                               FStar_Syntax_Syntax.fvar uu____13098
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____13100 =
                               let uu____13111 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____13111]  in
                             (uu____13095, uu____13100)  in
                           FStar_Syntax_Syntax.Tm_app uu____13078  in
                         FStar_All.pipe_left mk1 uu____13077  in
                       (uu____13076, s))))
        | FStar_Parser_AST.NamedTyp (uu____13148,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____13157 =
              let uu____13158 = FStar_Syntax_Subst.compress tm  in
              uu____13158.FStar_Syntax_Syntax.n  in
            (match uu____13157 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____13166 =
                   let uu___285_13167 =
                     let uu____13168 =
                       let uu____13169 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____13169  in
                     FStar_Syntax_Util.exp_string uu____13168  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___285_13167.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___285_13167.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____13166, noaqs)
             | uu____13170 ->
                 let uu____13171 =
                   let uu____13176 =
                     let uu____13177 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____13177
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____13176)  in
                 FStar_Errors.raise_error uu____13171
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____13183 = desugar_term_aq env e  in
            (match uu____13183 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____13195 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____13195, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____13201 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____13202 =
              let uu____13203 =
                let uu____13212 = desugar_term env e  in (bv, b, uu____13212)
                 in
              [uu____13203]  in
            (uu____13201, uu____13202)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____13243 =
              let uu____13244 =
                let uu____13245 =
                  let uu____13252 = desugar_term env e  in (uu____13252, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____13245  in
              FStar_All.pipe_left mk1 uu____13244  in
            (uu____13243, noaqs)
        | uu____13257 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____13258 = desugar_formula env top  in
            (uu____13258, noaqs)
        | uu____13259 ->
            let uu____13260 =
              let uu____13265 =
                let uu____13266 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____13266  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____13265)  in
            FStar_Errors.raise_error uu____13260 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____13272 -> false
    | uu____13281 -> true

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
           (fun uu____13318  ->
              match uu____13318 with
              | (a,imp) ->
                  let uu____13331 = desugar_term env a  in
                  arg_withimp_e imp uu____13331))

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
        let is_requires uu____13363 =
          match uu____13363 with
          | (t1,uu____13369) ->
              let uu____13370 =
                let uu____13371 = unparen t1  in
                uu____13371.FStar_Parser_AST.tm  in
              (match uu____13370 with
               | FStar_Parser_AST.Requires uu____13372 -> true
               | uu____13379 -> false)
           in
        let is_ensures uu____13389 =
          match uu____13389 with
          | (t1,uu____13395) ->
              let uu____13396 =
                let uu____13397 = unparen t1  in
                uu____13397.FStar_Parser_AST.tm  in
              (match uu____13396 with
               | FStar_Parser_AST.Ensures uu____13398 -> true
               | uu____13405 -> false)
           in
        let is_app head1 uu____13420 =
          match uu____13420 with
          | (t1,uu____13426) ->
              let uu____13427 =
                let uu____13428 = unparen t1  in
                uu____13428.FStar_Parser_AST.tm  in
              (match uu____13427 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____13430;
                      FStar_Parser_AST.level = uu____13431;_},uu____13432,uu____13433)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____13434 -> false)
           in
        let is_smt_pat uu____13444 =
          match uu____13444 with
          | (t1,uu____13450) ->
              let uu____13451 =
                let uu____13452 = unparen t1  in
                uu____13452.FStar_Parser_AST.tm  in
              (match uu____13451 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____13455);
                             FStar_Parser_AST.range = uu____13456;
                             FStar_Parser_AST.level = uu____13457;_},uu____13458)::uu____13459::[])
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
                             FStar_Parser_AST.range = uu____13498;
                             FStar_Parser_AST.level = uu____13499;_},uu____13500)::uu____13501::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____13526 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____13558 = head_and_args t1  in
          match uu____13558 with
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
                   let thunk_ens uu____13656 =
                     match uu____13656 with
                     | (e,i) ->
                         let uu____13667 = thunk_ens_ e  in (uu____13667, i)
                      in
                   let fail_lemma uu____13679 =
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
                         let uu____13759 =
                           let uu____13766 =
                             let uu____13773 = thunk_ens ens  in
                             [uu____13773; nil_pat]  in
                           req_true :: uu____13766  in
                         unit_tm :: uu____13759
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____13820 =
                           let uu____13827 =
                             let uu____13834 = thunk_ens ens  in
                             [uu____13834; nil_pat]  in
                           req :: uu____13827  in
                         unit_tm :: uu____13820
                     | ens::smtpat::[] when
                         (((let uu____13883 = is_requires ens  in
                            Prims.op_Negation uu____13883) &&
                             (let uu____13885 = is_smt_pat ens  in
                              Prims.op_Negation uu____13885))
                            &&
                            (let uu____13887 = is_decreases ens  in
                             Prims.op_Negation uu____13887))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____13888 =
                           let uu____13895 =
                             let uu____13902 = thunk_ens ens  in
                             [uu____13902; smtpat]  in
                           req_true :: uu____13895  in
                         unit_tm :: uu____13888
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____13949 =
                           let uu____13956 =
                             let uu____13963 = thunk_ens ens  in
                             [uu____13963; nil_pat; dec]  in
                           req_true :: uu____13956  in
                         unit_tm :: uu____13949
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____14023 =
                           let uu____14030 =
                             let uu____14037 = thunk_ens ens  in
                             [uu____14037; smtpat; dec]  in
                           req_true :: uu____14030  in
                         unit_tm :: uu____14023
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____14097 =
                           let uu____14104 =
                             let uu____14111 = thunk_ens ens  in
                             [uu____14111; nil_pat; dec]  in
                           req :: uu____14104  in
                         unit_tm :: uu____14097
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____14171 =
                           let uu____14178 =
                             let uu____14185 = thunk_ens ens  in
                             [uu____14185; smtpat]  in
                           req :: uu____14178  in
                         unit_tm :: uu____14171
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____14250 =
                           let uu____14257 =
                             let uu____14264 = thunk_ens ens  in
                             [uu____14264; dec; smtpat]  in
                           req :: uu____14257  in
                         unit_tm :: uu____14250
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____14326 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____14326, args)
               | FStar_Parser_AST.Name l when
                   (let uu____14354 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____14354
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____14355 =
                     let uu____14362 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14362, [])  in
                   (uu____14355, args)
               | FStar_Parser_AST.Name l when
                   (let uu____14380 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____14380
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____14381 =
                     let uu____14388 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14388, [])  in
                   (uu____14381, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____14404 =
                     let uu____14411 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14411, [])  in
                   (uu____14404, [(t1, FStar_Parser_AST.Nothing)])
               | uu____14434 ->
                   let default_effect =
                     let uu____14436 = FStar_Options.ml_ish ()  in
                     if uu____14436
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____14439 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____14439
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____14441 =
                     let uu____14448 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14448, [])  in
                   (uu____14441, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____14471 = pre_process_comp_typ t  in
        match uu____14471 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____14520 =
                  let uu____14525 =
                    let uu____14526 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____14526
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____14525)  in
                fail1 uu____14520)
             else ();
             (let is_universe uu____14537 =
                match uu____14537 with
                | (uu____14542,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____14544 = FStar_Util.take is_universe args  in
              match uu____14544 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____14603  ->
                         match uu____14603 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____14610 =
                    let uu____14625 = FStar_List.hd args1  in
                    let uu____14634 = FStar_List.tl args1  in
                    (uu____14625, uu____14634)  in
                  (match uu____14610 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____14689 =
                         let is_decrease uu____14727 =
                           match uu____14727 with
                           | (t1,uu____14737) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____14747;
                                       FStar_Syntax_Syntax.vars = uu____14748;_},uu____14749::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____14788 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____14689 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____14904  ->
                                      match uu____14904 with
                                      | (t1,uu____14914) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____14923,(arg,uu____14925)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____14964 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____14981 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____14992 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____14992
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____14996 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____14996
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____15003 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____15003
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____15007 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____15007
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____15011 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____15011
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____15015 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____15015
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____15033 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____15033
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
                                                  let uu____15122 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____15122
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
                                            | uu____15143 -> pat  in
                                          let uu____15144 =
                                            let uu____15155 =
                                              let uu____15166 =
                                                let uu____15175 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____15175, aq)  in
                                              [uu____15166]  in
                                            ens :: uu____15155  in
                                          req :: uu____15144
                                      | uu____15216 -> rest2
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
        | uu____15240 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___286_15261 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___286_15261.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___286_15261.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___287_15303 = b  in
             {
               FStar_Parser_AST.b = (uu___287_15303.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___287_15303.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___287_15303.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____15366 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____15366)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____15379 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____15379 with
             | (env1,a1) ->
                 let a2 =
                   let uu___288_15389 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___288_15389.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___288_15389.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____15415 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____15429 =
                     let uu____15432 =
                       let uu____15433 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____15433]  in
                     no_annot_abs uu____15432 body2  in
                   FStar_All.pipe_left setpos uu____15429  in
                 let uu____15454 =
                   let uu____15455 =
                     let uu____15472 =
                       let uu____15475 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____15475
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____15476 =
                       let uu____15487 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____15487]  in
                     (uu____15472, uu____15476)  in
                   FStar_Syntax_Syntax.Tm_app uu____15455  in
                 FStar_All.pipe_left mk1 uu____15454)
        | uu____15526 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____15606 = q (rest, pats, body)  in
              let uu____15613 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____15606 uu____15613
                FStar_Parser_AST.Formula
               in
            let uu____15614 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____15614 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____15623 -> failwith "impossible"  in
      let uu____15626 =
        let uu____15627 = unparen f  in uu____15627.FStar_Parser_AST.tm  in
      match uu____15626 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____15634,uu____15635) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____15646,uu____15647) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15678 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____15678
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15714 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____15714
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____15757 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____15762 =
        FStar_List.fold_left
          (fun uu____15795  ->
             fun b  ->
               match uu____15795 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___289_15839 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___289_15839.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___289_15839.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___289_15839.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15854 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____15854 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___290_15872 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___290_15872.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___290_15872.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____15873 =
                               let uu____15880 =
                                 let uu____15885 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____15885)  in
                               uu____15880 :: out  in
                             (env2, uu____15873))
                    | uu____15896 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____15762 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____15967 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15967)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____15972 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15972)
      | FStar_Parser_AST.TVariable x ->
          let uu____15976 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____15976)
      | FStar_Parser_AST.NoName t ->
          let uu____15980 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____15980)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

and (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                   FStar_Pervasives_Native.option)
           FStar_Pervasives_Native.tuple2,FStar_Syntax_DsEnv.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun imp  ->
      fun uu___243_15988  ->
        match uu___243_15988 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____16010 = FStar_Syntax_Syntax.null_binder k  in
            (uu____16010, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16027 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16027 with
             | (env1,a1) ->
                 let uu____16044 =
                   let uu____16051 = trans_aqual env1 imp  in
                   ((let uu___291_16057 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___291_16057.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___291_16057.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____16051)
                    in
                 (uu____16044, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___244_16065  ->
      match uu___244_16065 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____16069 =
            let uu____16070 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____16070  in
          FStar_Pervasives_Native.Some uu____16069
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

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
               (fun uu___245_16106  ->
                  match uu___245_16106 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____16107 -> false))
           in
        let quals2 q =
          let uu____16120 =
            (let uu____16123 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____16123) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____16120
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____16137 = FStar_Ident.range_of_lid disc_name  in
                let uu____16138 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____16137;
                  FStar_Syntax_Syntax.sigquals = uu____16138;
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
            let uu____16177 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____16215  ->
                        match uu____16215 with
                        | (x,uu____16225) ->
                            let uu____16230 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____16230 with
                             | (field_name,uu____16238) ->
                                 let only_decl =
                                   ((let uu____16242 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____16242)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____16244 =
                                        let uu____16245 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____16245.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____16244)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____16261 =
                                       FStar_List.filter
                                         (fun uu___246_16265  ->
                                            match uu___246_16265 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____16266 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____16261
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___247_16279  ->
                                             match uu___247_16279 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____16280 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____16282 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____16282;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____16287 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____16287
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____16292 =
                                        let uu____16297 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____16297  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____16292;
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
                                      let uu____16301 =
                                        let uu____16302 =
                                          let uu____16309 =
                                            let uu____16312 =
                                              let uu____16313 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____16313
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____16312]  in
                                          ((false, [lb]), uu____16309)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____16302
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____16301;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____16177 FStar_List.flatten
  
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
            (lid,uu____16357,t,uu____16359,n1,uu____16361) when
            let uu____16366 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____16366 ->
            let uu____16367 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____16367 with
             | (formals,uu____16385) ->
                 (match formals with
                  | [] -> []
                  | uu____16414 ->
                      let filter_records uu___248_16430 =
                        match uu___248_16430 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____16433,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____16445 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____16447 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____16447 with
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
                      let uu____16457 = FStar_Util.first_N n1 formals  in
                      (match uu____16457 with
                       | (uu____16486,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____16520 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
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
                    let uu____16598 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____16598
                    then
                      let uu____16601 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____16601
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____16604 =
                      let uu____16609 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____16609  in
                    let uu____16610 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____16615 =
                          let uu____16618 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____16618  in
                        FStar_Syntax_Util.arrow typars uu____16615
                      else FStar_Syntax_Syntax.tun  in
                    let uu____16622 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____16604;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____16610;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____16622;
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
          let tycon_id uu___249_16673 =
            match uu___249_16673 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____16675,uu____16676) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____16686,uu____16687,uu____16688) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____16698,uu____16699,uu____16700) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____16730,uu____16731,uu____16732) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____16776) ->
                let uu____16777 =
                  let uu____16778 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16778  in
                FStar_Parser_AST.mk_term uu____16777 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____16780 =
                  let uu____16781 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16781  in
                FStar_Parser_AST.mk_term uu____16780 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____16783) ->
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
              | uu____16814 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____16822 =
                     let uu____16823 =
                       let uu____16830 = binder_to_term b  in
                       (out, uu____16830, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____16823  in
                   FStar_Parser_AST.mk_term uu____16822
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___250_16842 =
            match uu___250_16842 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____16898  ->
                       match uu____16898 with
                       | (x,t,uu____16909) ->
                           let uu____16914 =
                             let uu____16915 =
                               let uu____16920 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____16920, t)  in
                             FStar_Parser_AST.Annotated uu____16915  in
                           FStar_Parser_AST.mk_binder uu____16914
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____16922 =
                    let uu____16923 =
                      let uu____16924 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____16924  in
                    FStar_Parser_AST.mk_term uu____16923
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____16922 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____16928 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____16955  ->
                          match uu____16955 with
                          | (x,uu____16965,uu____16966) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____16928)
            | uu____17019 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___251_17058 =
            match uu___251_17058 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____17082 = typars_of_binders _env binders  in
                (match uu____17082 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____17118 =
                         let uu____17119 =
                           let uu____17120 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____17120  in
                         FStar_Parser_AST.mk_term uu____17119
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____17118 binders  in
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
            | uu____17131 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____17173 =
              FStar_List.fold_left
                (fun uu____17207  ->
                   fun uu____17208  ->
                     match (uu____17207, uu____17208) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____17277 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____17277 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____17173 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____17368 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____17368
                | uu____17369 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____17377 = desugar_abstract_tc quals env [] tc  in
              (match uu____17377 with
               | (uu____17390,uu____17391,se,uu____17393) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____17396,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____17413 =
                                 let uu____17414 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____17414  in
                               if uu____17413
                               then
                                 let uu____17415 =
                                   let uu____17420 =
                                     let uu____17421 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____17421
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____17420)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____17415
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
                           | uu____17430 ->
                               let uu____17431 =
                                 let uu____17438 =
                                   let uu____17439 =
                                     let uu____17454 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____17454)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____17439
                                    in
                                 FStar_Syntax_Syntax.mk uu____17438  in
                               uu____17431 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___292_17470 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___292_17470.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___292_17470.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___292_17470.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____17471 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____17474 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____17474
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____17487 = typars_of_binders env binders  in
              (match uu____17487 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17521 =
                           FStar_Util.for_some
                             (fun uu___252_17523  ->
                                match uu___252_17523 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____17524 -> false) quals
                            in
                         if uu____17521
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____17529 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____17529
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____17534 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___253_17538  ->
                               match uu___253_17538 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____17539 -> false))
                        in
                     if uu____17534
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____17548 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____17548
                     then
                       let uu____17551 =
                         let uu____17558 =
                           let uu____17559 = unparen t  in
                           uu____17559.FStar_Parser_AST.tm  in
                         match uu____17558 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____17580 =
                               match FStar_List.rev args with
                               | (last_arg,uu____17610)::args_rev ->
                                   let uu____17622 =
                                     let uu____17623 = unparen last_arg  in
                                     uu____17623.FStar_Parser_AST.tm  in
                                   (match uu____17622 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____17651 -> ([], args))
                               | uu____17660 -> ([], args)  in
                             (match uu____17580 with
                              | (cattributes,args1) ->
                                  let uu____17699 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____17699))
                         | uu____17710 -> (t, [])  in
                       match uu____17551 with
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
                                  (fun uu___254_17732  ->
                                     match uu___254_17732 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____17733 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____17740)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____17764 = tycon_record_as_variant trec  in
              (match uu____17764 with
               | (t,fs) ->
                   let uu____17781 =
                     let uu____17784 =
                       let uu____17785 =
                         let uu____17794 =
                           let uu____17797 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____17797  in
                         (uu____17794, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____17785  in
                     uu____17784 :: quals  in
                   desugar_tycon env d uu____17781 [t])
          | uu____17802::uu____17803 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____17970 = et  in
                match uu____17970 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____18195 ->
                         let trec = tc  in
                         let uu____18219 = tycon_record_as_variant trec  in
                         (match uu____18219 with
                          | (t,fs) ->
                              let uu____18278 =
                                let uu____18281 =
                                  let uu____18282 =
                                    let uu____18291 =
                                      let uu____18294 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____18294  in
                                    (uu____18291, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____18282
                                   in
                                uu____18281 :: quals1  in
                              collect_tcs uu____18278 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____18381 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____18381 with
                          | (env2,uu____18441,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____18590 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____18590 with
                          | (env2,uu____18650,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____18775 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____18822 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____18822 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___256_19327  ->
                             match uu___256_19327 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____19392,uu____19393);
                                    FStar_Syntax_Syntax.sigrng = uu____19394;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____19395;
                                    FStar_Syntax_Syntax.sigmeta = uu____19396;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____19397;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____19460 =
                                     typars_of_binders env1 binders  in
                                   match uu____19460 with
                                   | (env2,tpars1) ->
                                       let uu____19487 =
                                         push_tparams env2 tpars1  in
                                       (match uu____19487 with
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
                                 let uu____19516 =
                                   let uu____19535 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____19535)
                                    in
                                 [uu____19516]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____19595);
                                    FStar_Syntax_Syntax.sigrng = uu____19596;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____19598;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____19599;_},constrs,tconstr,quals1)
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
                                 let uu____19697 = push_tparams env1 tpars
                                    in
                                 (match uu____19697 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____19764  ->
                                             match uu____19764 with
                                             | (x,uu____19776) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____19780 =
                                        let uu____19807 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____19915  ->
                                                  match uu____19915 with
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
                                                        let uu____19969 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____19969
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
                                                                uu___255_19980
                                                                 ->
                                                                match uu___255_19980
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____19992
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____20000 =
                                                        let uu____20019 =
                                                          let uu____20020 =
                                                            let uu____20021 =
                                                              let uu____20036
                                                                =
                                                                let uu____20037
                                                                  =
                                                                  let uu____20040
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____20040
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____20037
                                                                 in
                                                              (name, univs1,
                                                                uu____20036,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____20021
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____20020;
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
                                                          uu____20019)
                                                         in
                                                      (name, uu____20000)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____19807
                                         in
                                      (match uu____19780 with
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
                             | uu____20255 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____20381  ->
                             match uu____20381 with
                             | (name_doc,uu____20407,uu____20408) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____20480  ->
                             match uu____20480 with
                             | (uu____20499,uu____20500,se) -> se))
                      in
                   let uu____20526 =
                     let uu____20533 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____20533 rng
                      in
                   (match uu____20526 with
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
                               (fun uu____20595  ->
                                  match uu____20595 with
                                  | (uu____20616,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____20663,tps,k,uu____20666,constrs)
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
                                  | uu____20685 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____20702  ->
                                 match uu____20702 with
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
      let uu____20745 =
        FStar_List.fold_left
          (fun uu____20780  ->
             fun b  ->
               match uu____20780 with
               | (env1,binders1) ->
                   let uu____20824 = desugar_binder env1 b  in
                   (match uu____20824 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____20847 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____20847 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____20900 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____20745 with
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
          let uu____21001 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___257_21006  ->
                    match uu___257_21006 with
                    | FStar_Syntax_Syntax.Reflectable uu____21007 -> true
                    | uu____21008 -> false))
             in
          if uu____21001
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____21011 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____21011
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
      let uu____21043 = FStar_Syntax_Util.head_and_args at1  in
      match uu____21043 with
      | (hd1,args) ->
          let uu____21094 =
            let uu____21109 =
              let uu____21110 = FStar_Syntax_Subst.compress hd1  in
              uu____21110.FStar_Syntax_Syntax.n  in
            (uu____21109, args)  in
          (match uu____21094 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____21133)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr
               ->
               let uu____21168 =
                 let uu____21173 =
                   let uu____21182 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____21182 a1  in
                 uu____21173 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____21168 with
                | FStar_Pervasives_Native.Some [] ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Error_EmptyFailErrs,
                        "Found ill-applied fail, argument should be a non-empty list of integers")
                      at1.FStar_Syntax_Syntax.pos
                | FStar_Pervasives_Native.Some es ->
                    let uu____21216 =
                      let uu____21223 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____21223, false)  in
                    FStar_Pervasives_Native.Some uu____21216
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____21272) when
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
           | uu____21328 -> FStar_Pervasives_Native.None)
  
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
                  let uu____21497 = desugar_binders monad_env eff_binders  in
                  match uu____21497 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____21536 =
                          let uu____21537 =
                            let uu____21546 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____21546  in
                          FStar_List.length uu____21537  in
                        uu____21536 = (Prims.parse_int "1")  in
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
                            (uu____21592,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____21594,uu____21595,uu____21596),uu____21597)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____21630 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____21631 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____21643 = name_of_eff_decl decl  in
                             FStar_List.mem uu____21643 mandatory_members)
                          eff_decls
                         in
                      (match uu____21631 with
                       | (mandatory_members_decls,actions) ->
                           let uu____21660 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____21689  ->
                                     fun decl  ->
                                       match uu____21689 with
                                       | (env2,out) ->
                                           let uu____21709 =
                                             desugar_decl env2 decl  in
                                           (match uu____21709 with
                                            | (env3,ses) ->
                                                let uu____21722 =
                                                  let uu____21725 =
                                                    FStar_List.hd ses  in
                                                  uu____21725 :: out  in
                                                (env3, uu____21722)))
                                  (env1, []))
                              in
                           (match uu____21660 with
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
                                              (uu____21793,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21796,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____21797,
                                                                  (def,uu____21799)::
                                                                  (cps_type,uu____21801)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____21802;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____21803;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____21855 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21855 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21893 =
                                                     let uu____21894 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21895 =
                                                       let uu____21896 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21896
                                                        in
                                                     let uu____21903 =
                                                       let uu____21904 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21904
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21894;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21895;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____21903
                                                     }  in
                                                   (uu____21893, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____21913,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21916,defn),doc1)::[])
                                              when for_free ->
                                              let uu____21951 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21951 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21989 =
                                                     let uu____21990 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21991 =
                                                       let uu____21992 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21992
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21990;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21991;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____21989, doc1))
                                          | uu____22001 ->
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
                                    let uu____22033 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____22033
                                     in
                                  let uu____22034 =
                                    let uu____22035 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____22035
                                     in
                                  ([], uu____22034)  in
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
                                      let uu____22052 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____22052)  in
                                    let uu____22059 =
                                      let uu____22060 =
                                        let uu____22061 =
                                          let uu____22062 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22062
                                           in
                                        let uu____22071 = lookup1 "return"
                                           in
                                        let uu____22072 = lookup1 "bind"  in
                                        let uu____22073 =
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
                                            uu____22061;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____22071;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____22072;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____22073
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____22060
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____22059;
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
                                         (fun uu___258_22079  ->
                                            match uu___258_22079 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____22080 -> true
                                            | uu____22081 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____22095 =
                                       let uu____22096 =
                                         let uu____22097 =
                                           lookup1 "return_wp"  in
                                         let uu____22098 = lookup1 "bind_wp"
                                            in
                                         let uu____22099 =
                                           lookup1 "if_then_else"  in
                                         let uu____22100 = lookup1 "ite_wp"
                                            in
                                         let uu____22101 = lookup1 "stronger"
                                            in
                                         let uu____22102 = lookup1 "close_wp"
                                            in
                                         let uu____22103 = lookup1 "assert_p"
                                            in
                                         let uu____22104 = lookup1 "assume_p"
                                            in
                                         let uu____22105 = lookup1 "null_wp"
                                            in
                                         let uu____22106 = lookup1 "trivial"
                                            in
                                         let uu____22107 =
                                           if rr
                                           then
                                             let uu____22108 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____22108
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____22124 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____22126 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____22128 =
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
                                             uu____22097;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____22098;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____22099;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____22100;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____22101;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____22102;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____22103;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____22104;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____22105;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____22106;
                                           FStar_Syntax_Syntax.repr =
                                             uu____22107;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____22124;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____22126;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____22128
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____22096
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____22095;
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
                                          fun uu____22154  ->
                                            match uu____22154 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____22168 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____22168
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
                let uu____22192 = desugar_binders env1 eff_binders  in
                match uu____22192 with
                | (env2,binders) ->
                    let uu____22229 =
                      let uu____22240 = head_and_args defn  in
                      match uu____22240 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____22277 ->
                                let uu____22278 =
                                  let uu____22283 =
                                    let uu____22284 =
                                      let uu____22285 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____22285 " not found"
                                       in
                                    Prims.strcat "Effect " uu____22284  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____22283)
                                   in
                                FStar_Errors.raise_error uu____22278
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____22287 =
                            match FStar_List.rev args with
                            | (last_arg,uu____22317)::args_rev ->
                                let uu____22329 =
                                  let uu____22330 = unparen last_arg  in
                                  uu____22330.FStar_Parser_AST.tm  in
                                (match uu____22329 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____22358 -> ([], args))
                            | uu____22367 -> ([], args)  in
                          (match uu____22287 with
                           | (cattributes,args1) ->
                               let uu____22410 = desugar_args env2 args1  in
                               let uu____22411 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____22410, uu____22411))
                       in
                    (match uu____22229 with
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
                          (let uu____22447 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____22447 with
                           | (ed_binders,uu____22461,ed_binders_opening) ->
                               let sub1 uu____22474 =
                                 match uu____22474 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____22488 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____22488 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____22492 =
                                       let uu____22493 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____22493)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____22492
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____22502 =
                                   let uu____22503 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____22503
                                    in
                                 let uu____22518 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____22519 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____22520 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____22521 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____22522 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____22523 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____22524 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____22525 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____22526 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____22527 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____22528 =
                                   let uu____22529 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____22529
                                    in
                                 let uu____22544 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____22545 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____22546 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____22554 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____22555 =
                                          let uu____22556 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22556
                                           in
                                        let uu____22571 =
                                          let uu____22572 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22572
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____22554;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____22555;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____22571
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
                                     uu____22502;
                                   FStar_Syntax_Syntax.ret_wp = uu____22518;
                                   FStar_Syntax_Syntax.bind_wp = uu____22519;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____22520;
                                   FStar_Syntax_Syntax.ite_wp = uu____22521;
                                   FStar_Syntax_Syntax.stronger = uu____22522;
                                   FStar_Syntax_Syntax.close_wp = uu____22523;
                                   FStar_Syntax_Syntax.assert_p = uu____22524;
                                   FStar_Syntax_Syntax.assume_p = uu____22525;
                                   FStar_Syntax_Syntax.null_wp = uu____22526;
                                   FStar_Syntax_Syntax.trivial = uu____22527;
                                   FStar_Syntax_Syntax.repr = uu____22528;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____22544;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____22545;
                                   FStar_Syntax_Syntax.actions = uu____22546;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____22589 =
                                     let uu____22590 =
                                       let uu____22599 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____22599
                                        in
                                     FStar_List.length uu____22590  in
                                   uu____22589 = (Prims.parse_int "1")  in
                                 let uu____22630 =
                                   let uu____22633 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____22633 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____22630;
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
                                             let uu____22655 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____22655
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____22657 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____22657
                                 then
                                   let reflect_lid =
                                     let uu____22661 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____22661
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
    let uu____22671 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____22671 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____22722 ->
              let uu____22723 =
                let uu____22724 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____22724
                 in
              Prims.strcat "\n  " uu____22723
          | uu____22725 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____22738  ->
               match uu____22738 with
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
          let uu____22756 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____22756
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____22758 =
          let uu____22769 = FStar_Syntax_Syntax.as_arg arg  in [uu____22769]
           in
        FStar_Syntax_Util.mk_app fv uu____22758

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22800 = desugar_decl_noattrs env d  in
      match uu____22800 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____22818 = mk_comment_attr d  in uu____22818 :: attrs1  in
          let uu____22819 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___293_22825 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___293_22825.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___293_22825.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___293_22825.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___293_22825.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___294_22827 = sigelt  in
                      let uu____22828 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____22834 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____22834) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___294_22827.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___294_22827.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___294_22827.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___294_22827.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____22828
                      })) sigelts
             in
          (env1, uu____22819)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22855 = desugar_decl_aux env d  in
      match uu____22855 with
      | (env1,ses) ->
          let uu____22866 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____22866)

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
      | FStar_Parser_AST.Fsdoc uu____22894 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____22902 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____22902, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____22939  ->
                 match uu____22939 with | (x,uu____22947) -> x) tcs
             in
          let uu____22952 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____22952 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____22974;
                    FStar_Parser_AST.prange = uu____22975;_},uu____22976)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____22985;
                    FStar_Parser_AST.prange = uu____22986;_},uu____22987)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____23002;
                         FStar_Parser_AST.prange = uu____23003;_},uu____23004);
                    FStar_Parser_AST.prange = uu____23005;_},uu____23006)::[]
                   -> false
               | (p,uu____23034)::[] ->
                   let uu____23043 = is_app_pattern p  in
                   Prims.op_Negation uu____23043
               | uu____23044 -> false)
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
            let uu____23117 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____23117 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____23129 =
                     let uu____23130 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____23130.FStar_Syntax_Syntax.n  in
                   match uu____23129 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____23140) ->
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
                         | uu____23173::uu____23174 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____23177 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___259_23192  ->
                                     match uu___259_23192 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____23195;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____23196;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____23197;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____23198;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____23199;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____23200;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____23201;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____23213;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____23214;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____23215;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____23216;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____23217;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____23218;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____23232 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____23263  ->
                                   match uu____23263 with
                                   | (uu____23276,(uu____23277,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____23232
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____23295 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____23295
                         then
                           let uu____23298 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___295_23312 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___296_23314 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___296_23314.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___296_23314.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___295_23312.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___295_23312.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___295_23312.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___295_23312.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___295_23312.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___295_23312.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____23298)
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
                   | uu____23341 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____23347 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____23366 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____23347 with
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
                       let uu___297_23402 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___297_23402.FStar_Parser_AST.prange)
                       }
                   | uu____23409 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___298_23416 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___298_23416.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___298_23416.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___298_23416.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____23452 id1 =
                   match uu____23452 with
                   | (env1,ses) ->
                       let main =
                         let uu____23473 =
                           let uu____23474 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____23474  in
                         FStar_Parser_AST.mk_term uu____23473
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
                       let uu____23524 = desugar_decl env1 id_decl  in
                       (match uu____23524 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____23542 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____23542 FStar_Util.set_elements
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
            let uu____23565 = close_fun env t  in
            desugar_term env uu____23565  in
          let quals1 =
            let uu____23569 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____23569
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____23575 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____23575;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____23583 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____23583 with
           | (t,uu____23597) ->
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
            let uu____23627 =
              let uu____23636 = FStar_Syntax_Syntax.null_binder t  in
              [uu____23636]  in
            let uu____23655 =
              let uu____23658 =
                let uu____23659 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____23659  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____23658
               in
            FStar_Syntax_Util.arrow uu____23627 uu____23655  in
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
            let uu____23720 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____23720 with
            | FStar_Pervasives_Native.None  ->
                let uu____23723 =
                  let uu____23728 =
                    let uu____23729 =
                      let uu____23730 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____23730 " not found"  in
                    Prims.strcat "Effect name " uu____23729  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____23728)  in
                FStar_Errors.raise_error uu____23723
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____23734 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____23752 =
                  let uu____23755 =
                    let uu____23756 = desugar_term env t  in
                    ([], uu____23756)  in
                  FStar_Pervasives_Native.Some uu____23755  in
                (uu____23752, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____23769 =
                  let uu____23772 =
                    let uu____23773 = desugar_term env wp  in
                    ([], uu____23773)  in
                  FStar_Pervasives_Native.Some uu____23772  in
                let uu____23780 =
                  let uu____23783 =
                    let uu____23784 = desugar_term env t  in
                    ([], uu____23784)  in
                  FStar_Pervasives_Native.Some uu____23783  in
                (uu____23769, uu____23780)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____23796 =
                  let uu____23799 =
                    let uu____23800 = desugar_term env t  in
                    ([], uu____23800)  in
                  FStar_Pervasives_Native.Some uu____23799  in
                (FStar_Pervasives_Native.None, uu____23796)
             in
          (match uu____23734 with
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
            let uu____23834 =
              let uu____23835 =
                let uu____23842 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____23842, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____23835  in
            {
              FStar_Syntax_Syntax.sigel = uu____23834;
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
      let uu____23868 =
        FStar_List.fold_left
          (fun uu____23888  ->
             fun d  ->
               match uu____23888 with
               | (env1,sigelts) ->
                   let uu____23908 = desugar_decl env1 d  in
                   (match uu____23908 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____23868 with
      | (env1,sigelts) ->
          let rec forward acc uu___261_23953 =
            match uu___261_23953 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____23967,FStar_Syntax_Syntax.Sig_let uu____23968) ->
                     let uu____23981 =
                       let uu____23984 =
                         let uu___299_23985 = se2  in
                         let uu____23986 =
                           let uu____23989 =
                             FStar_List.filter
                               (fun uu___260_24003  ->
                                  match uu___260_24003 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____24007;
                                           FStar_Syntax_Syntax.vars =
                                             uu____24008;_},uu____24009);
                                      FStar_Syntax_Syntax.pos = uu____24010;
                                      FStar_Syntax_Syntax.vars = uu____24011;_}
                                      when
                                      let uu____24038 =
                                        let uu____24039 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____24039
                                         in
                                      uu____24038 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____24040 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____23989
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___299_23985.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___299_23985.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___299_23985.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___299_23985.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____23986
                         }  in
                       uu____23984 :: se1 :: acc  in
                     forward uu____23981 sigelts1
                 | uu____24045 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____24053 = forward [] sigelts  in (env1, uu____24053)
  
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
          | (FStar_Pervasives_Native.None ,uu____24114) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____24118;
               FStar_Syntax_Syntax.exports = uu____24119;
               FStar_Syntax_Syntax.is_interface = uu____24120;_},FStar_Parser_AST.Module
             (current_lid,uu____24122)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____24130) ->
              let uu____24133 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____24133
           in
        let uu____24138 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____24174 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____24174, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____24191 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____24191, mname, decls, false)
           in
        match uu____24138 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____24221 = desugar_decls env2 decls  in
            (match uu____24221 with
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
          let uu____24283 =
            (FStar_Options.interactive ()) &&
              (let uu____24285 =
                 let uu____24286 =
                   let uu____24287 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____24287  in
                 FStar_Util.get_file_extension uu____24286  in
               FStar_List.mem uu____24285 ["fsti"; "fsi"])
             in
          if uu____24283 then as_interface m else m  in
        let uu____24291 = desugar_modul_common curmod env m1  in
        match uu____24291 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____24309 = FStar_Syntax_DsEnv.pop ()  in
              (uu____24309, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____24329 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____24329 with
      | (env1,modul,pop_when_done) ->
          let uu____24343 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____24343 with
           | (env2,modul1) ->
               ((let uu____24355 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____24355
                 then
                   let uu____24356 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____24356
                 else ());
                (let uu____24358 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____24358, modul1))))
  
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
        (fun uu____24405  ->
           let uu____24406 = desugar_modul env modul  in
           match uu____24406 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____24447  ->
           let uu____24448 = desugar_decls env decls  in
           match uu____24448 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____24502  ->
             let uu____24503 = desugar_partial_modul modul env a_modul  in
             match uu____24503 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____24601 ->
                  let t =
                    let uu____24611 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____24611  in
                  let uu____24624 =
                    let uu____24625 = FStar_Syntax_Subst.compress t  in
                    uu____24625.FStar_Syntax_Syntax.n  in
                  (match uu____24624 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____24637,uu____24638)
                       -> bs1
                   | uu____24663 -> failwith "Impossible")
               in
            let uu____24672 =
              let uu____24679 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____24679
                FStar_Syntax_Syntax.t_unit
               in
            match uu____24672 with
            | (binders,uu____24681,binders_opening) ->
                let erase_term t =
                  let uu____24689 =
                    let uu____24690 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____24690  in
                  FStar_Syntax_Subst.close binders uu____24689  in
                let erase_tscheme uu____24708 =
                  match uu____24708 with
                  | (us,t) ->
                      let t1 =
                        let uu____24728 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____24728 t  in
                      let uu____24731 =
                        let uu____24732 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____24732  in
                      ([], uu____24731)
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
                    | uu____24755 ->
                        let bs =
                          let uu____24765 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____24765  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____24805 =
                          let uu____24806 =
                            let uu____24809 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____24809  in
                          uu____24806.FStar_Syntax_Syntax.n  in
                        (match uu____24805 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____24811,uu____24812) -> bs1
                         | uu____24837 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____24844 =
                      let uu____24845 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____24845  in
                    FStar_Syntax_Subst.close binders uu____24844  in
                  let uu___300_24846 = action  in
                  let uu____24847 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____24848 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___300_24846.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___300_24846.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____24847;
                    FStar_Syntax_Syntax.action_typ = uu____24848
                  }  in
                let uu___301_24849 = ed  in
                let uu____24850 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____24851 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____24852 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____24853 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____24854 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____24855 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____24856 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____24857 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____24858 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____24859 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____24860 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____24861 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____24862 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____24863 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____24864 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____24865 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___301_24849.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___301_24849.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____24850;
                  FStar_Syntax_Syntax.signature = uu____24851;
                  FStar_Syntax_Syntax.ret_wp = uu____24852;
                  FStar_Syntax_Syntax.bind_wp = uu____24853;
                  FStar_Syntax_Syntax.if_then_else = uu____24854;
                  FStar_Syntax_Syntax.ite_wp = uu____24855;
                  FStar_Syntax_Syntax.stronger = uu____24856;
                  FStar_Syntax_Syntax.close_wp = uu____24857;
                  FStar_Syntax_Syntax.assert_p = uu____24858;
                  FStar_Syntax_Syntax.assume_p = uu____24859;
                  FStar_Syntax_Syntax.null_wp = uu____24860;
                  FStar_Syntax_Syntax.trivial = uu____24861;
                  FStar_Syntax_Syntax.repr = uu____24862;
                  FStar_Syntax_Syntax.return_repr = uu____24863;
                  FStar_Syntax_Syntax.bind_repr = uu____24864;
                  FStar_Syntax_Syntax.actions = uu____24865;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___301_24849.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___302_24881 = se  in
                  let uu____24882 =
                    let uu____24883 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____24883  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24882;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___302_24881.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___302_24881.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___302_24881.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___302_24881.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___303_24887 = se  in
                  let uu____24888 =
                    let uu____24889 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24889
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24888;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___303_24887.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___303_24887.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___303_24887.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___303_24887.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____24891 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____24892 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____24892 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____24904 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____24904
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____24906 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____24906)
  