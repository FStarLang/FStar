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
  fun uu___82_58  ->
    match uu___82_58 with
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
      fun uu___83_76  ->
        match uu___83_76 with
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
  fun uu___84_83  ->
    match uu___84_83 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___85_92  ->
    match uu___85_92 with
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
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____160 =
      let uu____161 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____161  in
    FStar_Parser_AST.mk_term uu____160 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____165 =
      let uu____166 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____166  in
    FStar_Parser_AST.mk_term uu____165 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____174 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____174 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____180) ->
          let uu____193 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____193 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____199,uu____200) ->
          is_comp_type env head1
      | FStar_Parser_AST.Ascribed (t1,uu____202,uu____203) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____208,t1) -> is_comp_type env t1
      | uu____210 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____220 =
          let uu____223 =
            let uu____224 =
              let uu____229 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____229, r)  in
            FStar_Ident.mk_ident uu____224  in
          [uu____223]  in
        FStar_All.pipe_right uu____220 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____237 .
    FStar_ToSyntax_Env.env ->
      Prims.int ->
        'Auu____237 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____265 =
              let uu____266 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____266 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____265  in
          let fallback uu____272 =
            match FStar_Ident.text_of_id op with
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
                let uu____275 = FStar_Options.ml_ish ()  in
                if uu____275
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
            | uu____279 -> FStar_Pervasives_Native.None  in
          let uu____280 =
            let uu____287 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_ToSyntax_Env.try_lookup_lid env uu____287  in
          match uu____280 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____299 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____315 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____315
  
let rec (free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____354 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____358 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____358 with | (env1,uu____370) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____373,term) ->
          let uu____375 = free_type_vars env term  in (env, uu____375)
      | FStar_Parser_AST.TAnnotated (id1,uu____381) ->
          let uu____382 = FStar_ToSyntax_Env.push_bv env id1  in
          (match uu____382 with | (env1,uu____394) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____398 = free_type_vars env t  in (env, uu____398)

and (free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Labeled uu____407 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____417 = FStar_ToSyntax_Env.try_lookup_id env a  in
          (match uu____417 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____430 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____437 -> []
      | FStar_Parser_AST.Uvar uu____438 -> []
      | FStar_Parser_AST.Var uu____439 -> []
      | FStar_Parser_AST.Projector uu____440 -> []
      | FStar_Parser_AST.Discrim uu____445 -> []
      | FStar_Parser_AST.Name uu____446 -> []
      | FStar_Parser_AST.Requires (t1,uu____448) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____454) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____459,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____474,ts) ->
          FStar_List.collect
            (fun uu____495  ->
               match uu____495 with | (t1,uu____503) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____504,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____512) ->
          let uu____513 = free_type_vars env t1  in
          let uu____516 = free_type_vars env t2  in
          FStar_List.append uu____513 uu____516
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____521 = free_type_vars_b env b  in
          (match uu____521 with
           | (env1,f) ->
               let uu____536 = free_type_vars env1 t1  in
               FStar_List.append f uu____536)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____545 =
            FStar_List.fold_left
              (fun uu____565  ->
                 fun binder  ->
                   match uu____565 with
                   | (env1,free) ->
                       let uu____585 = free_type_vars_b env1 binder  in
                       (match uu____585 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____545 with
           | (env1,free) ->
               let uu____616 = free_type_vars env1 body  in
               FStar_List.append free uu____616)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____625 =
            FStar_List.fold_left
              (fun uu____645  ->
                 fun binder  ->
                   match uu____645 with
                   | (env1,free) ->
                       let uu____665 = free_type_vars_b env1 binder  in
                       (match uu____665 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____625 with
           | (env1,free) ->
               let uu____696 = free_type_vars env1 body  in
               FStar_List.append free uu____696)
      | FStar_Parser_AST.Project (t1,uu____700) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____704 -> []
      | FStar_Parser_AST.Let uu____711 -> []
      | FStar_Parser_AST.LetOpen uu____732 -> []
      | FStar_Parser_AST.If uu____737 -> []
      | FStar_Parser_AST.QForall uu____744 -> []
      | FStar_Parser_AST.QExists uu____757 -> []
      | FStar_Parser_AST.Record uu____770 -> []
      | FStar_Parser_AST.Match uu____783 -> []
      | FStar_Parser_AST.TryWith uu____798 -> []
      | FStar_Parser_AST.Bind uu____813 -> []
      | FStar_Parser_AST.Seq uu____820 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      match t1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____908 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____928 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____928  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____946 =
                     let uu____947 =
                       let uu____952 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____952)  in
                     FStar_Parser_AST.TAnnotated uu____947  in
                   FStar_Parser_AST.mk_binder uu____946 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
  
let (close_fun :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____965 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____965  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____983 =
                     let uu____984 =
                       let uu____989 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____989)  in
                     FStar_Parser_AST.TAnnotated uu____984  in
                   FStar_Parser_AST.mk_binder uu____983 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Product uu____991 -> t
           | uu____998 ->
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
      | uu____1030 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1036,uu____1037) -> true
    | FStar_Parser_AST.PatVar (uu____1042,uu____1043) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1049) -> is_var_pattern p1
    | uu____1050 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1055) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1056;
           FStar_Parser_AST.prange = uu____1057;_},uu____1058)
        -> true
    | uu____1069 -> false
  
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                 p.FStar_Parser_AST.prange), unit_ty))
          p.FStar_Parser_AST.prange
    | uu____1073 -> p
  
let rec (destruct_app_pattern :
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either,FStar_Parser_AST.pattern
                                                                    Prims.list,
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1113 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1113 with
             | (name,args,uu____1144) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1170);
               FStar_Parser_AST.prange = uu____1171;_},args)
            when is_top_level1 ->
            let uu____1181 =
              let uu____1186 = FStar_ToSyntax_Env.qualify env id1  in
              FStar_Util.Inr uu____1186  in
            (uu____1181, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1196);
               FStar_Parser_AST.prange = uu____1197;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1215 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1253 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1254,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1257 -> acc
      | FStar_Parser_AST.PatTvar uu____1258 -> acc
      | FStar_Parser_AST.PatOp uu____1265 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1273) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1282) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1297 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1297
      | FStar_Parser_AST.PatAscribed (pat,uu____1305) ->
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
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1343 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1371 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___86_1397  ->
    match uu___86_1397 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1404 -> failwith "Impossible"
  
let (as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.binder,FStar_ToSyntax_Env.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun imp  ->
      fun uu___87_1429  ->
        match uu___87_1429 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1445 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1445, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1450 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____1450 with
             | (env1,a1) ->
                 (((let uu___111_1470 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___111_1470.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___111_1470.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
  
type env_t = FStar_ToSyntax_Env.env[@@deriving show]
type lenv_t = FStar_Syntax_Syntax.bv Prims.list[@@deriving show]
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list,(FStar_Syntax_Syntax.bv,
                                                                    FStar_Syntax_Syntax.fv)
                                                                    FStar_Util.either,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                           FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple4 -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____1495  ->
    match uu____1495 with
    | (attrs,n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = attrs
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
      let uu____1560 =
        let uu____1575 =
          let uu____1576 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1576  in
        let uu____1577 =
          let uu____1586 =
            let uu____1593 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1593)  in
          [uu____1586]  in
        (uu____1575, uu____1577)  in
      FStar_Syntax_Syntax.Tm_app uu____1560  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1626 =
        let uu____1641 =
          let uu____1642 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1642  in
        let uu____1643 =
          let uu____1652 =
            let uu____1659 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1659)  in
          [uu____1652]  in
        (uu____1641, uu____1643)  in
      FStar_Syntax_Syntax.Tm_app uu____1626  in
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
          let uu____1702 =
            let uu____1717 =
              let uu____1718 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____1718  in
            let uu____1719 =
              let uu____1728 =
                let uu____1735 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____1735)  in
              let uu____1738 =
                let uu____1747 =
                  let uu____1754 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____1754)  in
                [uu____1747]  in
              uu____1728 :: uu____1738  in
            (uu____1717, uu____1719)  in
          FStar_Syntax_Syntax.Tm_app uu____1702  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___88_1785  ->
    match uu___88_1785 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1786 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1794 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1794)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  ->
        let uu____1809 =
          let uu____1810 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____1810  in
        FStar_Util.Inr uu____1809
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1821)) ->
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
             let uu____1887 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1887
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1898 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1898
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1909 =
               let uu____1914 =
                 let uu____1915 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____1915
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____1914)
                in
             FStar_Errors.raise_error uu____1909 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____1920 ->
        let rec aux t1 univargs =
          match t1.FStar_Parser_AST.tm with
          | FStar_Parser_AST.App (t2,targ,uu____1956) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___89_1980  ->
                     match uu___89_1980 with
                     | FStar_Util.Inr uu____1985 -> true
                     | uu____1986 -> false) univargs
              then
                let uu____1991 =
                  let uu____1992 =
                    FStar_List.map
                      (fun uu___90_2001  ->
                         match uu___90_2001 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____1992  in
                FStar_Util.Inr uu____1991
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___91_2018  ->
                        match uu___91_2018 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2024 -> failwith "impossible")
                     univargs
                    in
                 let uu____2025 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2025)
          | uu____2031 ->
              let uu____2032 =
                let uu____2037 =
                  let uu____2038 =
                    let uu____2039 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2039 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2038  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2037)  in
              FStar_Errors.raise_error uu____2032 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2048 ->
        let uu____2049 =
          let uu____2054 =
            let uu____2055 =
              let uu____2056 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2056 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2055  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2054)  in
        FStar_Errors.raise_error uu____2049 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields :
  'Auu____2075 .
    FStar_ToSyntax_Env.env ->
      (FStar_Ident.lident,'Auu____2075) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_ToSyntax_Env.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2100 = FStar_List.hd fields  in
        match uu____2100 with
        | (f,uu____2110) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2120 =
                match uu____2120 with
                | (f',uu____2126) ->
                    (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
                     (let uu____2128 =
                        FStar_ToSyntax_Env.belongs_to_record env f' record
                         in
                      if uu____2128
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                             f'.FStar_Ident.str
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                             msg) rg)))
                 in
              (let uu____2132 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2132);
              (match () with | () -> record)))
  
let rec (desugar_data_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool ->
        (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 r =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____2349 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2356 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2357 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2359,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2400  ->
                          match uu____2400 with
                          | (p3,uu____2410) ->
                              let uu____2411 =
                                let uu____2412 =
                                  let uu____2415 = pat_vars p3  in
                                  FStar_Util.set_intersect uu____2415 out  in
                                FStar_Util.set_is_empty uu____2412  in
                              if uu____2411
                              then
                                let uu____2420 = pat_vars p3  in
                                FStar_Util.set_union out uu____2420
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                                    "Non-linear patterns are not permitted.")
                                  r) FStar_Syntax_Syntax.no_names)
             in
          pat_vars p1  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2427) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2428) -> ()
         | (true ,uu____2435) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____2470 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2470 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2484 ->
               let uu____2487 = push_bv_maybe_mut e x  in
               (match uu____2487 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2574 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2590 =
                 let uu____2591 =
                   let uu____2592 =
                     let uu____2599 =
                       let uu____2600 =
                         let uu____2605 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2605, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2600  in
                     (uu____2599, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2592  in
                 {
                   FStar_Parser_AST.pat = uu____2591;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2590
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2610 = aux loc env1 p2  in
               (match uu____2610 with
                | (loc1,env',binder,p3,imp) ->
                    let annot_pat_var p4 t1 =
                      match p4.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let uu___112_2664 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var
                                 (let uu___113_2669 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___113_2669.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___113_2669.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___112_2664.FStar_Syntax_Syntax.p)
                          }
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let uu___114_2671 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild
                                 (let uu___115_2676 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___115_2676.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___115_2676.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___114_2671.FStar_Syntax_Syntax.p)
                          }
                      | uu____2677 when top -> p4
                      | uu____2678 ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                              "Type ascriptions within patterns are only allowed on variables")
                            orig.FStar_Parser_AST.prange
                       in
                    let uu____2681 =
                      match binder with
                      | LetBinder uu____2694 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2708 = close_fun env1 t  in
                            desugar_term env1 uu____2708  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2710 -> true)
                           then
                             (let uu____2711 =
                                let uu____2716 =
                                  let uu____2717 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____2718 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____2719 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3
                                    "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                    uu____2717 uu____2718 uu____2719
                                   in
                                (FStar_Errors.Warning_MultipleAscriptions,
                                  uu____2716)
                                 in
                              FStar_Errors.log_issue
                                orig.FStar_Parser_AST.prange uu____2711)
                           else ();
                           (let uu____2721 = annot_pat_var p3 t1  in
                            (uu____2721,
                              (LocalBinder
                                 ((let uu___116_2727 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___116_2727.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___116_2727.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }), aq)))))
                       in
                    (match uu____2681 with
                     | (p4,binder1) -> (loc1, env', binder1, p4, imp)))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2749 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2749, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2760 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2760, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2781 = resolvex loc env1 x  in
               (match uu____2781 with
                | (loc1,env2,xbv) ->
                    let uu____2803 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2803, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2824 = resolvex loc env1 x  in
               (match uu____2824 with
                | (loc1,env2,xbv) ->
                    let uu____2846 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2846, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l
                  in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2858 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2858, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2882;_},args)
               ->
               let uu____2888 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2929  ->
                        match uu____2929 with
                        | (loc1,env2,args1) ->
                            let uu____2977 = aux loc1 env2 arg  in
                            (match uu____2977 with
                             | (loc2,env3,uu____3006,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____2888 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    let uu____3076 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3076, false))
           | FStar_Parser_AST.PatApp uu____3093 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3115 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3148  ->
                        match uu____3148 with
                        | (loc1,env2,pats1) ->
                            let uu____3180 = aux loc1 env2 pat  in
                            (match uu____3180 with
                             | (loc2,env3,uu____3205,pat1,uu____3207) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3115 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3250 =
                        let uu____3253 =
                          let uu____3258 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3258  in
                        let uu____3259 =
                          let uu____3260 =
                            let uu____3273 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3273, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3260  in
                        FStar_All.pipe_left uu____3253 uu____3259  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3305 =
                               let uu____3306 =
                                 let uu____3319 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3319, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3306  in
                             FStar_All.pipe_left (pos_r r) uu____3305) pats1
                        uu____3250
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
               let uu____3363 =
                 FStar_List.fold_left
                   (fun uu____3403  ->
                      fun p2  ->
                        match uu____3403 with
                        | (loc1,env2,pats) ->
                            let uu____3452 = aux loc1 env2 p2  in
                            (match uu____3452 with
                             | (loc2,env3,uu____3481,pat,uu____3483) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3363 with
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
                    let uu____3578 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____3578 with
                     | (constr,uu____3600) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3603 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3605 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3605, false)))
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
                      (fun uu____3676  ->
                         match uu____3676 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3706  ->
                         match uu____3706 with
                         | (f,uu____3712) ->
                             let uu____3713 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3739  ->
                                       match uu____3739 with
                                       | (g,uu____3745) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____3713 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3750,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____3757 =
                   let uu____3758 =
                     let uu____3765 =
                       let uu____3766 =
                         let uu____3767 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____3767  in
                       FStar_Parser_AST.mk_pattern uu____3766
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____3765, args)  in
                   FStar_Parser_AST.PatApp uu____3758  in
                 FStar_Parser_AST.mk_pattern uu____3757
                   p1.FStar_Parser_AST.prange
                  in
               let uu____3770 = aux loc env1 app  in
               (match uu____3770 with
                | (env2,e,b,p2,uu____3799) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3827 =
                            let uu____3828 =
                              let uu____3841 =
                                let uu___117_3842 = fv  in
                                let uu____3843 =
                                  let uu____3846 =
                                    let uu____3847 =
                                      let uu____3854 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____3854)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3847
                                     in
                                  FStar_Pervasives_Native.Some uu____3846  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___117_3842.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___117_3842.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3843
                                }  in
                              (uu____3841, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____3828  in
                          FStar_All.pipe_left pos uu____3827
                      | uu____3881 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____3931 = aux' true loc env1 p2  in
               (match uu____3931 with
                | (loc1,env2,var,p3,uu____3958) ->
                    let uu____3963 =
                      FStar_List.fold_left
                        (fun uu____3995  ->
                           fun p4  ->
                             match uu____3995 with
                             | (loc2,env3,ps1) ->
                                 let uu____4028 = aux' true loc2 env3 p4  in
                                 (match uu____4028 with
                                  | (loc3,env4,uu____4053,p5,uu____4055) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____3963 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4106 ->
               let uu____4107 = aux' true loc env1 p1  in
               (match uu____4107 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4147 = aux_maybe_or env p  in
         match uu____4147 with
         | (env1,b,pats) ->
             ((let uu____4178 =
                 FStar_List.map
                   (fun pats1  ->
                      check_linear_pattern_variables pats1
                        p.FStar_Parser_AST.prange) pats
                  in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4178);
              (env1, b, pats)))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
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
            let uu____4215 =
              let uu____4216 =
                let uu____4221 = FStar_ToSyntax_Env.qualify env x  in
                (uu____4221, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____4216  in
            (env, uu____4215, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4241 =
                  let uu____4242 =
                    let uu____4247 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4247, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4242  in
                mklet uu____4241
            | FStar_Parser_AST.PatVar (x,uu____4249) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4255);
                   FStar_Parser_AST.prange = uu____4256;_},t)
                ->
                let uu____4262 =
                  let uu____4263 =
                    let uu____4268 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____4269 = desugar_term env t  in
                    (uu____4268, uu____4269)  in
                  LetBinder uu____4263  in
                (env, uu____4262, [])
            | uu____4272 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4282 = desugar_data_pat env p is_mut  in
             match uu____4282 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4311;
                       FStar_Syntax_Syntax.p = uu____4312;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4317;
                       FStar_Syntax_Syntax.p = uu____4318;_}::[] -> []
                   | uu____4323 -> p1  in
                 (env1, binder, p2))

and (desugar_binding_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple3)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        (env_t,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun uu____4330  ->
    fun env  ->
      fun pat  ->
        let uu____4333 = desugar_data_pat env pat false  in
        match uu____4333 with | (env1,uu____4349,pat1) -> (env1, pat1)

and (desugar_match_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and (desugar_term :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and (desugar_typ :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env true  in
      desugar_term_maybe_top false env1 e

and (desugar_machine_integer :
  FStar_ToSyntax_Env.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____4367  ->
        fun range  ->
          match uu____4367 with
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
              ((let uu____4377 =
                  let uu____4378 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4378  in
                if uu____4377
                then
                  let uu____4379 =
                    let uu____4384 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4384)  in
                  FStar_Errors.log_issue range uu____4379
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
                  FStar_Ident.lid_of_path (FStar_Ident.path_of_text intro_nm)
                    range
                   in
                let lid1 =
                  let uu____4392 = FStar_ToSyntax_Env.try_lookup_lid env lid
                     in
                  match uu____4392 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4402) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             FStar_Ident.lid_of_path
                               (FStar_Ident.path_of_text private_intro_nm)
                               range
                              in
                           let private_fv =
                             let uu____4412 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4412 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___118_4413 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___118_4413.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___118_4413.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4414 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4421 =
                        let uu____4426 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4426)
                         in
                      FStar_Errors.raise_error uu____4421 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4442 =
                  let uu____4445 =
                    let uu____4446 =
                      let uu____4461 =
                        let uu____4470 =
                          let uu____4477 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4477)  in
                        [uu____4470]  in
                      (lid1, uu____4461)  in
                    FStar_Syntax_Syntax.Tm_app uu____4446  in
                  FStar_Syntax_Syntax.mk uu____4445  in
                uu____4442 FStar_Pervasives_Native.None range))

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
            let uu____4516 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid_with_attributes
                  else
                    FStar_ToSyntax_Env.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4516 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____4562;
                              FStar_Syntax_Syntax.vars = uu____4563;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____4586 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4586 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____4594 =
                                 let uu____4595 =
                                   let uu____4598 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____4598  in
                                 uu____4595.FStar_Syntax_Syntax.n  in
                               match uu____4594 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____4614))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____4615 -> msg
                             else msg  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____4619 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4619 " is deprecated"  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____4620 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____4625 =
                      let uu____4626 =
                        let uu____4633 = mk_ref_read tm1  in
                        (uu____4633,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____4626  in
                    FStar_All.pipe_left mk1 uu____4625
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        match t.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4649; FStar_Ident.ident = uu____4650;
              FStar_Ident.nsstr = uu____4651; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4654 ->
            let uu____4655 =
              let uu____4660 =
                let uu____4661 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____4661  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____4660)  in
            FStar_Errors.raise_error uu____4655 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes

and (desugar_term_maybe_top :
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term) =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let setpos e =
          let uu___119_4681 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___119_4681.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___119_4681.FStar_Syntax_Syntax.vars)
          }  in
        match top.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4684 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            desugar_machine_integer env i size top.FStar_Parser_AST.range
        | FStar_Parser_AST.Const c -> mk1 (FStar_Syntax_Syntax.Tm_constant c)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("==", r)), args))
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level
               in
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op (op_star,uu____4735::uu____4736::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4740 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____4740 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4753;_},t1::t2::[])
                  ->
                  let uu____4758 = flatten1 t1  in
                  FStar_List.append uu____4758 [t2]
              | uu____4761 -> [t]  in
            let targs =
              let uu____4765 = flatten1 top  in
              FStar_All.pipe_right uu____4765
                (FStar_List.map
                   (fun t  ->
                      let uu____4775 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____4775))
               in
            let uu____4776 =
              let uu____4781 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4781
               in
            (match uu____4776 with
             | (tup,uu____4787) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4791 =
              let uu____4794 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              FStar_Pervasives_Native.fst uu____4794  in
            FStar_All.pipe_left setpos uu____4791
        | FStar_Parser_AST.Uvar u ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedUniverseVariable,
                (Prims.strcat "Unexpected universe variable "
                   (Prims.strcat (FStar_Ident.text_of_id u)
                      " in non-universe context")))
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4814 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____4814 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     (Prims.strcat "Unexpected or unbound operator: "
                        (FStar_Ident.text_of_id s)))
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____4846 = desugar_term env t  in
                             (uu____4846, FStar_Pervasives_Native.None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4860)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4875 =
              let uu___120_4876 = top  in
              let uu____4877 =
                let uu____4878 =
                  let uu____4885 =
                    let uu___121_4886 = top  in
                    let uu____4887 =
                      let uu____4888 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4888  in
                    {
                      FStar_Parser_AST.tm = uu____4887;
                      FStar_Parser_AST.range =
                        (uu___121_4886.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___121_4886.FStar_Parser_AST.level)
                    }  in
                  (uu____4885, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4878  in
              {
                FStar_Parser_AST.tm = uu____4877;
                FStar_Parser_AST.range =
                  (uu___120_4876.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___120_4876.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4875
        | FStar_Parser_AST.Construct (n1,(a,uu____4891)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____4907 =
                let uu___122_4908 = top  in
                let uu____4909 =
                  let uu____4910 =
                    let uu____4917 =
                      let uu___123_4918 = top  in
                      let uu____4919 =
                        let uu____4920 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____4920  in
                      {
                        FStar_Parser_AST.tm = uu____4919;
                        FStar_Parser_AST.range =
                          (uu___123_4918.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___123_4918.FStar_Parser_AST.level)
                      }  in
                    (uu____4917, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____4910  in
                {
                  FStar_Parser_AST.tm = uu____4909;
                  FStar_Parser_AST.range =
                    (uu___122_4908.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___122_4908.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____4907))
        | FStar_Parser_AST.Construct (n1,(a,uu____4923)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4938 =
              let uu___124_4939 = top  in
              let uu____4940 =
                let uu____4941 =
                  let uu____4948 =
                    let uu___125_4949 = top  in
                    let uu____4950 =
                      let uu____4951 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4951  in
                    {
                      FStar_Parser_AST.tm = uu____4950;
                      FStar_Parser_AST.range =
                        (uu___125_4949.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___125_4949.FStar_Parser_AST.level)
                    }  in
                  (uu____4948, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4941  in
              {
                FStar_Parser_AST.tm = uu____4940;
                FStar_Parser_AST.range =
                  (uu___124_4939.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___124_4939.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4938
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4952; FStar_Ident.ident = uu____4953;
              FStar_Ident.nsstr = uu____4954; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4957; FStar_Ident.ident = uu____4958;
              FStar_Ident.nsstr = uu____4959; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4962; FStar_Ident.ident = uu____4963;
               FStar_Ident.nsstr = uu____4964; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____4982 =
              let uu____4983 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____4983  in
            mk1 uu____4982
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4984; FStar_Ident.ident = uu____4985;
              FStar_Ident.nsstr = uu____4986; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4989; FStar_Ident.ident = uu____4990;
              FStar_Ident.nsstr = uu____4991; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4994; FStar_Ident.ident = uu____4995;
              FStar_Ident.nsstr = uu____4996; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5001;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5003 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
              match uu____5003 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____5008 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____5008))
        | FStar_Parser_AST.Var l ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Name l ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____5023 = FStar_ToSyntax_Env.try_lookup_datacon env l
                   in
                match uu____5023 with
                | FStar_Pervasives_Native.Some uu____5032 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5037 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l
                       in
                    (match uu____5037 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5051 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5064 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____5064
              | uu____5065 ->
                  let uu____5072 =
                    let uu____5077 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____5077)  in
                  FStar_Errors.raise_error uu____5072
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____5080 = FStar_ToSyntax_Env.try_lookup_datacon env lid
                 in
              match uu____5080 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5083 =
                    let uu____5088 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____5088)
                     in
                  FStar_Errors.raise_error uu____5083
                    top.FStar_Parser_AST.range
              | uu____5089 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____5108 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____5108 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____5112 =
                    let uu____5119 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                       in
                    (uu____5119, true)  in
                  (match uu____5112 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5134 ->
                            let uu____5141 =
                              FStar_Util.take
                                (fun uu____5165  ->
                                   match uu____5165 with
                                   | (uu____5170,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args
                               in
                            (match uu____5141 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes
                                    in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____5234  ->
                                        match uu____5234 with
                                        | (t,imp) ->
                                            let te = desugar_term env t  in
                                            arg_withimp_e imp te) args1
                                    in
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let app =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 if is_data
                                 then
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (app,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Data_app)))
                                 else app)))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____5281 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l  in
                    match uu____5281 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____5288 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5295 =
              FStar_List.fold_left
                (fun uu____5340  ->
                   fun b  ->
                     match uu____5340 with
                     | (env1,tparams,typs) ->
                         let uu____5397 = desugar_binder env1 b  in
                         (match uu____5397 with
                          | (xopt,t1) ->
                              let uu____5426 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5435 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____5435)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____5426 with
                               | (env2,x) ->
                                   let uu____5455 =
                                     let uu____5458 =
                                       let uu____5461 =
                                         let uu____5462 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5462
                                          in
                                       [uu____5461]  in
                                     FStar_List.append typs uu____5458  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___126_5488 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___126_5488.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___126_5488.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5455)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____5295 with
             | (env1,uu____5512,targs) ->
                 let uu____5534 =
                   let uu____5539 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5539
                    in
                 (match uu____5534 with
                  | (tup,uu____5545) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5556 = uncurry binders t  in
            (match uu____5556 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___92_5588 =
                   match uu___92_5588 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____5602 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____5602
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____5624 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____5624 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5639 = desugar_binder env b  in
            (match uu____5639 with
             | (FStar_Pervasives_Native.None ,uu____5646) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5656 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____5656 with
                  | ((x,uu____5662),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____5669 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____5669))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____5689 =
              FStar_List.fold_left
                (fun uu____5709  ->
                   fun pat  ->
                     match uu____5709 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5735,t) ->
                              let uu____5737 =
                                let uu____5740 = free_type_vars env1 t  in
                                FStar_List.append uu____5740 ftvs  in
                              (env1, uu____5737)
                          | uu____5745 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____5689 with
             | (uu____5750,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____5762 =
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
                   FStar_List.append uu____5762 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___93_5803 =
                   match uu___93_5803 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5841 =
                                 let uu____5842 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____5842
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____5841 body1  in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1  in
                       let uu____5895 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____5895
                   | p::rest ->
                       let uu____5906 = desugar_binding_pat env1 p  in
                       (match uu____5906 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5930 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____5935 =
                              match b with
                              | LetBinder uu____5968 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____6018) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6054 =
                                          let uu____6059 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____6059, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____6054
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6095,uu____6096) ->
                                             let tup2 =
                                               let uu____6098 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6098
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6102 =
                                                 let uu____6105 =
                                                   let uu____6106 =
                                                     let uu____6121 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____6124 =
                                                       let uu____6127 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____6128 =
                                                         let uu____6131 =
                                                           let uu____6132 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6132
                                                            in
                                                         [uu____6131]  in
                                                       uu____6127 ::
                                                         uu____6128
                                                        in
                                                     (uu____6121, uu____6124)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6106
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6105
                                                  in
                                               uu____6102
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____6143 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6143
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6174,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6176,pats)) ->
                                             let tupn =
                                               let uu____6215 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6215
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6225 =
                                                 let uu____6226 =
                                                   let uu____6241 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____6244 =
                                                     let uu____6253 =
                                                       let uu____6262 =
                                                         let uu____6263 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6263
                                                          in
                                                       [uu____6262]  in
                                                     FStar_List.append args
                                                       uu____6253
                                                      in
                                                   (uu____6241, uu____6244)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6226
                                                  in
                                               mk1 uu____6225  in
                                             let p2 =
                                               let uu____6283 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6283
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6318 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____5935 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6385,uu____6386,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              match e.FStar_Parser_AST.tm with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____6405 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____6409 ->
            let rec aux args e =
              match e.FStar_Parser_AST.tm with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6453 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6453  in
                  aux (arg :: args) e1
              | uu____6466 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let tac_bind_lid =
              FStar_Ident.lid_of_path ["FStar"; "Tactics"; "Effect"; "bind"]
                x.FStar_Ident.idRange
               in
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
            let uu____6494 =
              FStar_ToSyntax_Env.resolve_to_fully_qualified_name env bind_lid
               in
            (match uu____6494 with
             | FStar_Pervasives_Native.Some flid when
                 FStar_Ident.lid_equals flid tac_bind_lid ->
                 let r =
                   FStar_Parser_AST.mk_term
                     (FStar_Parser_AST.Const
                        (FStar_Const.Const_range (t2.FStar_Parser_AST.range)))
                     t2.FStar_Parser_AST.range FStar_Parser_AST.Expr
                    in
                 let uu____6499 =
                   FStar_Parser_AST.mkExplicitApp bind1 [r; t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6499
             | uu____6500 ->
                 let uu____6503 =
                   FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6503)
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6506 =
              let uu____6507 =
                let uu____6514 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [(FStar_Pervasives_Native.None,
                               ((FStar_Parser_AST.mk_pattern
                                   FStar_Parser_AST.PatWild
                                   t1.FStar_Parser_AST.range), t1))], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____6514,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____6507  in
            mk1 uu____6506
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            let uu____6566 =
              let uu____6571 = FStar_ToSyntax_Env.expect_typ env1  in
              if uu____6571 then desugar_typ else desugar_term  in
            uu____6566 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____6614 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6739  ->
                        match uu____6739 with
                        | (attr_opt,(p,def)) ->
                            let uu____6791 = is_app_pattern p  in
                            if uu____6791
                            then
                              let uu____6816 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____6816, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6880 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____6880, def1)
                               | uu____6913 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____6945);
                                           FStar_Parser_AST.prange =
                                             uu____6946;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____6976 =
                                            let uu____6991 =
                                              let uu____6996 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____6996  in
                                            (uu____6991, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____6976, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____7051) ->
                                        if top_level
                                        then
                                          let uu____7080 =
                                            let uu____7095 =
                                              let uu____7100 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7100  in
                                            (uu____7095, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____7080, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____7154 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____7179 =
                FStar_List.fold_left
                  (fun uu____7246  ->
                     fun uu____7247  ->
                       match (uu____7246, uu____7247) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____7343,uu____7344),uu____7345))
                           ->
                           let uu____7438 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7464 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____7464 with
                                  | (env2,xx) ->
                                      let uu____7483 =
                                        let uu____7486 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____7486 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____7483))
                             | FStar_Util.Inr l ->
                                 let uu____7494 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____7494, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____7438 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____7179 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____7626 =
                    match uu____7626 with
                    | (attrs_opt,(uu____7656,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7708 = is_comp_type env1 t  in
                                if uu____7708
                                then
                                  ((let uu____7710 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7720 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____7720))
                                       in
                                    match uu____7710 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____7723 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7725 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____7725))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____7723
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____7729 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7729 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7733 ->
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
                              let uu____7748 =
                                let uu____7749 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7749
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____7748
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
                          (attrs, lbname1, FStar_Syntax_Syntax.tun, body2)
                     in
                  let lbs1 =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs
                     in
                  let body1 = desugar_term env' body  in
                  let uu____7803 =
                    let uu____7804 =
                      let uu____7817 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs1), uu____7817)  in
                    FStar_Syntax_Syntax.Tm_let uu____7804  in
                  FStar_All.pipe_left mk1 uu____7803
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
              let uu____7871 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____7871 with
              | (env1,binder,pat1) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____7898 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7898
                            FStar_Pervasives_Native.None
                           in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [mk_lb (attrs, (FStar_Util.Inr fv), t, t12)]),
                               body1))
                    | LocalBinder (x,uu____7918) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat1 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7921;
                              FStar_Syntax_Syntax.p = uu____7922;_}::[] ->
                              body1
                          | uu____7927 ->
                              let uu____7930 =
                                let uu____7933 =
                                  let uu____7934 =
                                    let uu____7957 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____7958 =
                                      desugar_disjunctive_pattern pat1
                                        FStar_Pervasives_Native.None body1
                                       in
                                    (uu____7957, uu____7958)  in
                                  FStar_Syntax_Syntax.Tm_match uu____7934  in
                                FStar_Syntax_Syntax.mk uu____7933  in
                              uu____7930 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range
                           in
                        let uu____7968 =
                          let uu____7969 =
                            let uu____7982 =
                              let uu____7983 =
                                let uu____7984 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____7984]  in
                              FStar_Syntax_Subst.close uu____7983 body2  in
                            ((false,
                               [mk_lb
                                  (attrs, (FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____7982)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____7969  in
                        FStar_All.pipe_left mk1 uu____7968
                     in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm
               in
            let uu____8012 = FStar_List.hd lbs  in
            (match uu____8012 with
             | (attrs,(head_pat,defn)) ->
                 let uu____8052 = is_rec || (is_app_pattern head_pat)  in
                 if uu____8052
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____8061 =
                let uu____8062 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____8062  in
              mk1 uu____8061  in
            let uu____8063 =
              let uu____8064 =
                let uu____8087 =
                  let uu____8090 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____8090
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None)
                   in
                let uu____8111 =
                  let uu____8126 =
                    let uu____8139 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range
                       in
                    let uu____8142 = desugar_term env t2  in
                    (uu____8139, FStar_Pervasives_Native.None, uu____8142)
                     in
                  let uu____8151 =
                    let uu____8166 =
                      let uu____8179 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range
                         in
                      let uu____8182 = desugar_term env t3  in
                      (uu____8179, FStar_Pervasives_Native.None, uu____8182)
                       in
                    [uu____8166]  in
                  uu____8126 :: uu____8151  in
                (uu____8087, uu____8111)  in
              FStar_Syntax_Syntax.Tm_match uu____8064  in
            mk1 uu____8063
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
            desugar_term env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____8323 =
              match uu____8323 with
              | (pat,wopt,b) ->
                  let uu____8341 = desugar_match_pat env pat  in
                  (match uu____8341 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8362 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____8362
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____8364 =
              let uu____8365 =
                let uu____8388 = desugar_term env e  in
                let uu____8389 = FStar_List.collect desugar_branch branches
                   in
                (uu____8388, uu____8389)  in
              FStar_Syntax_Syntax.Tm_match uu____8365  in
            FStar_All.pipe_left mk1 uu____8364
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8418 = is_comp_type env t  in
              if uu____8418
              then
                let uu____8425 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____8425
              else
                (let uu____8431 = desugar_term env t  in
                 FStar_Util.Inl uu____8431)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____8437 =
              let uu____8438 =
                let uu____8465 = desugar_term env e  in
                (uu____8465, (annot, tac_opt1), FStar_Pervasives_Native.None)
                 in
              FStar_Syntax_Syntax.Tm_ascribed uu____8438  in
            FStar_All.pipe_left mk1 uu____8437
        | FStar_Parser_AST.Record (uu____8490,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____8527 = FStar_List.hd fields  in
              match uu____8527 with | (f,uu____8539) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8581  ->
                        match uu____8581 with
                        | (g,uu____8587) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____8593,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8607 =
                         let uu____8612 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____8612)
                          in
                       FStar_Errors.raise_error uu____8607
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
                   [record.FStar_ToSyntax_Env.constrname])
               in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8620 =
                    let uu____8631 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8662  ->
                              match uu____8662 with
                              | (f,uu____8672) ->
                                  let uu____8673 =
                                    let uu____8674 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8674
                                     in
                                  (uu____8673, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____8631)  in
                  FStar_Parser_AST.Construct uu____8620
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____8692 =
                      let uu____8693 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____8693  in
                    FStar_Parser_AST.mk_term uu____8692 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____8695 =
                      let uu____8708 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8738  ->
                                match uu____8738 with
                                | (f,uu____8748) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____8708)  in
                    FStar_Parser_AST.Record uu____8695  in
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
            let e = desugar_term env recterm1  in
            (match e.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_meta
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____8810;
                         FStar_Syntax_Syntax.vars = uu____8811;_},args);
                    FStar_Syntax_Syntax.pos = uu____8813;
                    FStar_Syntax_Syntax.vars = uu____8814;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8842 =
                     let uu____8843 =
                       let uu____8858 =
                         let uu____8859 =
                           let uu____8862 =
                             let uu____8863 =
                               let uu____8870 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____8870)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____8863  in
                           FStar_Pervasives_Native.Some uu____8862  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____8859
                          in
                       (uu____8858, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____8843  in
                   FStar_All.pipe_left mk1 uu____8842  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8901 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8905 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
                 in
              match uu____8905 with
              | (constrname,is_rec) ->
                  let e1 = desugar_term env e  in
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
                  let uu____8924 =
                    let uu____8925 =
                      let uu____8940 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual
                         in
                      let uu____8941 =
                        let uu____8944 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____8944]  in
                      (uu____8940, uu____8941)  in
                    FStar_Syntax_Syntax.Tm_app uu____8925  in
                  FStar_All.pipe_left mk1 uu____8924))
        | FStar_Parser_AST.NamedTyp (uu____8949,e) -> desugar_term env e
        | uu____8951 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8952 ->
            let uu____8953 =
              let uu____8958 =
                let uu____8959 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term" uu____8959  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____8958)  in
            FStar_Errors.raise_error uu____8953 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8961 -> false
    | uu____8970 -> true

and (is_synth_by_tactic :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____8976 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid  in
          (match uu____8976 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____8980 -> false

and (desugar_args :
  FStar_ToSyntax_Env.env ->
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
           (fun uu____9017  ->
              match uu____9017 with
              | (a,imp) ->
                  let uu____9030 = desugar_term env a  in
                  arg_withimp_e imp uu____9030))

and (desugar_comp :
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail a err = FStar_Errors.raise_error err r  in
        let is_requires uu____9056 =
          match uu____9056 with
          | (t1,uu____9062) ->
              (match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Requires uu____9063 -> true
               | uu____9070 -> false)
           in
        let is_ensures uu____9078 =
          match uu____9078 with
          | (t1,uu____9084) ->
              (match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Ensures uu____9085 -> true
               | uu____9092 -> false)
           in
        let is_app head1 uu____9103 =
          match uu____9103 with
          | (t1,uu____9109) ->
              (match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____9111;
                      FStar_Parser_AST.level = uu____9112;_},uu____9113,uu____9114)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____9115 -> false)
           in
        let is_smt_pat uu____9123 =
          match uu____9123 with
          | (t1,uu____9129) ->
              (match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____9132);
                             FStar_Parser_AST.range = uu____9133;
                             FStar_Parser_AST.level = uu____9134;_},uu____9135)::uu____9136::[])
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
                             FStar_Parser_AST.range = uu____9175;
                             FStar_Parser_AST.level = uu____9176;_},uu____9177)::uu____9178::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____9203 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____9231 = head_and_args t1  in
          match uu____9231 with
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
                   let thunk_ens uu____9325 =
                     match uu____9325 with
                     | (e,i) ->
                         let uu____9336 = thunk_ens_ e  in (uu____9336, i)
                      in
                   let fail_lemma uu____9346 =
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
                         let uu____9426 =
                           let uu____9433 =
                             let uu____9440 = thunk_ens ens  in
                             [uu____9440; nil_pat]  in
                           req_true :: uu____9433  in
                         unit_tm :: uu____9426
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____9487 =
                           let uu____9494 =
                             let uu____9501 = thunk_ens ens  in
                             [uu____9501; nil_pat]  in
                           req :: uu____9494  in
                         unit_tm :: uu____9487
                     | ens::smtpat::[] when
                         (((Prims.op_Negation (is_requires ens)) &&
                             (let uu____9549 = is_smt_pat ens  in
                              Prims.op_Negation uu____9549))
                            && (Prims.op_Negation (is_decreases ens)))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____9550 =
                           let uu____9557 =
                             let uu____9564 = thunk_ens ens  in
                             [uu____9564; smtpat]  in
                           req_true :: uu____9557  in
                         unit_tm :: uu____9550
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____9611 =
                           let uu____9618 =
                             let uu____9625 = thunk_ens ens  in
                             [uu____9625; nil_pat; dec]  in
                           req_true :: uu____9618  in
                         unit_tm :: uu____9611
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9685 =
                           let uu____9692 =
                             let uu____9699 = thunk_ens ens  in
                             [uu____9699; smtpat; dec]  in
                           req_true :: uu____9692  in
                         unit_tm :: uu____9685
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____9759 =
                           let uu____9766 =
                             let uu____9773 = thunk_ens ens  in
                             [uu____9773; nil_pat; dec]  in
                           req :: uu____9766  in
                         unit_tm :: uu____9759
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9833 =
                           let uu____9840 =
                             let uu____9847 = thunk_ens ens  in
                             [uu____9847; smtpat]  in
                           req :: uu____9840  in
                         unit_tm :: uu____9833
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____9912 =
                           let uu____9919 =
                             let uu____9926 = thunk_ens ens  in
                             [uu____9926; dec; smtpat]  in
                           req :: uu____9919  in
                         unit_tm :: uu____9912
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____9988 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____9988, args)
               | FStar_Parser_AST.Name l when
                   (let uu____10016 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____10016
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____10034 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____10034
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_GTot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])
               | uu____10072 ->
                   let default_effect =
                     let uu____10074 = FStar_Options.ml_ish ()  in
                     if uu____10074
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____10077 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____10077
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____10101 = pre_process_comp_typ t  in
        match uu____10101 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____10150 =
                       let uu____10155 =
                         let uu____10156 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____10156
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____10155)
                        in
                     fail () uu____10150)
                else Obj.repr ());
             (let is_universe uu____10165 =
                match uu____10165 with
                | (uu____10170,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____10172 = FStar_Util.take is_universe args  in
              match uu____10172 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____10231  ->
                         match uu____10231 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____10238 =
                    let uu____10253 = FStar_List.hd args1  in
                    let uu____10262 = FStar_List.tl args1  in
                    (uu____10253, uu____10262)  in
                  (match uu____10238 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____10317 =
                         let is_decrease uu____10353 =
                           match uu____10353 with
                           | (t1,uu____10363) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____10373;
                                       FStar_Syntax_Syntax.vars = uu____10374;_},uu____10375::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10406 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____10317 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10520  ->
                                      match uu____10520 with
                                      | (t1,uu____10530) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10539,(arg,uu____10541)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10570 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____10583 -> false  in
                              (((is_empty () (Obj.magic decreases_clause)) &&
                                  (is_empty () (Obj.magic rest2)))
                                 && (is_empty () (Obj.magic cattributes)))
                                && (is_empty () (Obj.magic universes1))
                               in
                            if
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              if
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_GTot_lid)
                              then FStar_Syntax_Syntax.mk_GTotal result_typ
                              else
                                (let flags1 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then [FStar_Syntax_Syntax.LEMMA]
                                   else
                                     if
                                       FStar_Ident.lid_equals eff
                                         FStar_Parser_Const.effect_Tot_lid
                                     then [FStar_Syntax_Syntax.TOTAL]
                                     else
                                       if
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_ML_lid
                                       then [FStar_Syntax_Syntax.MLEFFECT]
                                       else
                                         if
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_GTot_lid
                                         then
                                           [FStar_Syntax_Syntax.SOMETRIVIAL]
                                         else []
                                    in
                                 let flags2 =
                                   FStar_List.append flags1 cattributes  in
                                 let rest3 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
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
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
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
                                           | uu____10723 -> pat  in
                                         let uu____10724 =
                                           let uu____10735 =
                                             let uu____10746 =
                                               let uu____10755 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____10755, aq)  in
                                             [uu____10746]  in
                                           ens :: uu____10735  in
                                         req :: uu____10724
                                     | uu____10796 -> rest2
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
                                   })))))

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
        | uu____10818 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___127_10835 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___127_10835.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___127_10835.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___128_10869 = b  in
             {
               FStar_Parser_AST.b = (uu___128_10869.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___128_10869.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___128_10869.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10928 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10928)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10941 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____10941 with
             | (env1,a1) ->
                 let a2 =
                   let uu___129_10951 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___129_10951.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___129_10951.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____10973 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____10987 =
                     let uu____10990 =
                       let uu____10991 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____10991]  in
                     no_annot_abs uu____10990 body2  in
                   FStar_All.pipe_left setpos uu____10987  in
                 let uu____10996 =
                   let uu____10997 =
                     let uu____11012 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____11013 =
                       let uu____11016 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____11016]  in
                     (uu____11012, uu____11013)  in
                   FStar_Syntax_Syntax.Tm_app uu____10997  in
                 FStar_All.pipe_left mk1 uu____10996)
        | uu____11021 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____11093 = q (rest, pats, body)  in
              let uu____11100 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____11093 uu____11100
                FStar_Parser_AST.Formula
               in
            let uu____11101 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____11101 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____11110 -> failwith "impossible"  in
      match f.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____11119,uu____11120) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____11131,uu____11132) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11163 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____11163
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11199 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____11199
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | uu____11241 -> desugar_term env f

and (typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                        FStar_Pervasives_Native.option)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____11246 =
        FStar_List.fold_left
          (fun uu____11282  ->
             fun b  ->
               match uu____11282 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___130_11334 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___130_11334.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___130_11334.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___130_11334.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11351 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____11351 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___131_11371 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_11371.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_11371.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11388 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____11246 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and (desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____11475 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11475)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11480 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11480)
      | FStar_Parser_AST.TVariable x ->
          let uu____11484 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____11484)
      | FStar_Parser_AST.NoName t ->
          let uu____11492 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____11492)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

let (mk_data_discriminators :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun quals  ->
    fun env  ->
      fun datas  ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___94_11525  ->
                  match uu___94_11525 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11526 -> false))
           in
        let quals2 q =
          let uu____11537 =
            (let uu____11540 = FStar_ToSyntax_Env.iface env  in
             Prims.op_Negation uu____11540) ||
              (FStar_ToSyntax_Env.admitted_iface env)
             in
          if uu____11537
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____11553 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____11553;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }))
  
let (mk_indexed_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_ToSyntax_Env.env ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
            let p = FStar_Ident.range_of_lid lid  in
            let uu____11584 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11614  ->
                        match uu____11614 with
                        | (x,uu____11622) ->
                            let uu____11623 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____11623 with
                             | (field_name,uu____11631) ->
                                 let only_decl =
                                   ((let uu____11635 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11635)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11637 =
                                        let uu____11638 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____11638.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____11637)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11652 =
                                       FStar_List.filter
                                         (fun uu___95_11656  ->
                                            match uu___95_11656 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11657 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11652
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___96_11670  ->
                                             match uu___96_11670 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11671 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name);
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____11679 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____11679
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____11684 =
                                        let uu____11689 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____11689  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11684;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbattrs = []
                                      }  in
                                    let impl =
                                      let uu____11693 =
                                        let uu____11694 =
                                          let uu____11701 =
                                            let uu____11704 =
                                              let uu____11705 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____11705
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____11704]  in
                                          ((false, [lb]), uu____11701)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11694
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11693;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____11584 FStar_List.flatten
  
let (mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____11749,t,uu____11751,n1,uu____11753) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11758 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____11758 with
             | (formals,uu____11774) ->
                 (match formals with
                  | [] -> []
                  | uu____11797 ->
                      let filter_records uu___97_11809 =
                        match uu___97_11809 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11812,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11824 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____11826 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____11826 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____11836 = FStar_Util.first_N n1 formals  in
                      (match uu____11836 with
                       | (uu____11859,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11885 -> []
  
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
                    let uu____11935 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____11935
                    then
                      let uu____11938 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____11938
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____11941 =
                      let uu____11946 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____11946  in
                    let uu____11947 =
                      let uu____11950 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____11950  in
                    let uu____11953 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11941;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11947;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____11953;
                      FStar_Syntax_Syntax.lbattrs = []
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
  FStar_ToSyntax_Env.env ->
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
          let tycon_id uu___98_12000 =
            match uu___98_12000 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____12002,uu____12003) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____12013,uu____12014,uu____12015) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____12025,uu____12026,uu____12027) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____12057,uu____12058,uu____12059) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____12101) ->
                let uu____12102 =
                  let uu____12103 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12103  in
                FStar_Parser_AST.mk_term uu____12102 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____12105 =
                  let uu____12106 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12106  in
                FStar_Parser_AST.mk_term uu____12105 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____12108) ->
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
              | uu____12131 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____12137 =
                     let uu____12138 =
                       let uu____12145 = binder_to_term b  in
                       (out, uu____12145, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____12138  in
                   FStar_Parser_AST.mk_term uu____12137
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___99_12155 =
            match uu___99_12155 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____12210  ->
                       match uu____12210 with
                       | (x,t,uu____12221) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____12227 =
                    let uu____12228 =
                      let uu____12229 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____12229  in
                    FStar_Parser_AST.mk_term uu____12228
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____12227 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____12233 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____12260  ->
                          match uu____12260 with
                          | (x,uu____12270,uu____12271) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____12233)
            | uu____12324 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___100_12355 =
            match uu___100_12355 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____12379 = typars_of_binders _env binders  in
                (match uu____12379 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____12425 =
                         let uu____12426 =
                           let uu____12427 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____12427  in
                         FStar_Parser_AST.mk_term uu____12426
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____12425 binders  in
                     let qlid = FStar_ToSyntax_Env.qualify _env id1  in
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
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env'
                         id1 FStar_Syntax_Syntax.Delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____12440 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____12484 =
              FStar_List.fold_left
                (fun uu____12524  ->
                   fun uu____12525  ->
                     match (uu____12524, uu____12525) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12616 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____12616 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____12484 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12729 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____12729
                | uu____12730 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____12738 = desugar_abstract_tc quals env [] tc  in
              (match uu____12738 with
               | (uu____12751,uu____12752,se,uu____12754) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12757,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12774 =
                                 let uu____12775 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____12775  in
                               if uu____12774
                               then
                                 let uu____12776 =
                                   let uu____12781 =
                                     let uu____12782 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____12782
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____12781)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12776
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
                           | uu____12789 ->
                               let uu____12790 =
                                 let uu____12793 =
                                   let uu____12794 =
                                     let uu____12807 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____12807)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12794
                                    in
                                 FStar_Syntax_Syntax.mk uu____12793  in
                               uu____12790 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___132_12811 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___132_12811.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___132_12811.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___132_12811.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12814 -> failwith "Impossible"  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   let env2 =
                     let uu____12817 = FStar_ToSyntax_Env.qualify env1 id1
                        in
                     FStar_ToSyntax_Env.push_doc env1 uu____12817
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____12832 = typars_of_binders env binders  in
              (match uu____12832 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12868 =
                           FStar_Util.for_some
                             (fun uu___101_12870  ->
                                match uu___101_12870 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12871 -> false) quals
                            in
                         if uu____12868
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____12878 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___102_12882  ->
                               match uu___102_12882 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12883 -> false))
                        in
                     if uu____12878
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_ToSyntax_Env.qualify env id1  in
                   let se =
                     let uu____12892 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____12892
                     then
                       let uu____12895 =
                         match t.FStar_Parser_AST.tm with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12922 =
                               match FStar_List.rev args with
                               | (last_arg,uu____12952)::args_rev ->
                                   (match last_arg.FStar_Parser_AST.tm with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____12991 -> ([], args))
                               | uu____13000 -> ([], args)  in
                             (match uu____12922 with
                              | (cattributes,args1) ->
                                  let uu____13039 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____13039))
                         | uu____13050 -> (t, [])  in
                       match uu____12895 with
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
                                  (fun uu___103_13072  ->
                                     match uu___103_13072 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____13073 -> true))
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
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____13084)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____13108 = tycon_record_as_variant trec  in
              (match uu____13108 with
               | (t,fs) ->
                   let uu____13125 =
                     let uu____13128 =
                       let uu____13129 =
                         let uu____13138 =
                           let uu____13141 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____13141  in
                         (uu____13138, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____13129  in
                     uu____13128 :: quals  in
                   desugar_tycon env d uu____13125 [t])
          | uu____13146::uu____13147 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____13308 = et  in
                match uu____13308 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13533 ->
                         let trec = tc  in
                         let uu____13557 = tycon_record_as_variant trec  in
                         (match uu____13557 with
                          | (t,fs) ->
                              let uu____13616 =
                                let uu____13619 =
                                  let uu____13620 =
                                    let uu____13629 =
                                      let uu____13632 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____13632  in
                                    (uu____13629, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____13620
                                   in
                                uu____13619 :: quals1  in
                              collect_tcs uu____13616 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____13719 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____13719 with
                          | (env2,uu____13779,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____13928 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____13928 with
                          | (env2,uu____13988,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____14113 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____14160 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____14160 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___105_14671  ->
                             match uu___105_14671 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____14738,uu____14739);
                                    FStar_Syntax_Syntax.sigrng = uu____14740;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14741;
                                    FStar_Syntax_Syntax.sigmeta = uu____14742;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14743;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14804 =
                                     typars_of_binders env1 binders  in
                                   match uu____14804 with
                                   | (env2,tpars1) ->
                                       let uu____14835 =
                                         push_tparams env2 tpars1  in
                                       (match uu____14835 with
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
                                 let uu____14868 =
                                   let uu____14889 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____14889)
                                    in
                                 [uu____14868]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____14957);
                                    FStar_Syntax_Syntax.sigrng = uu____14958;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____14960;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14961;_},constrs,tconstr,quals1)
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
                                 let uu____15057 = push_tparams env1 tpars
                                    in
                                 (match uu____15057 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____15134  ->
                                             match uu____15134 with
                                             | (x,uu____15148) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____15156 =
                                        let uu____15185 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____15299  ->
                                                  match uu____15299 with
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
                                                        let uu____15355 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____15355
                                                         in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id1
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___104_15366
                                                                 ->
                                                                match uu___104_15366
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15378
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____15386 =
                                                        let uu____15407 =
                                                          let uu____15408 =
                                                            let uu____15409 =
                                                              let uu____15424
                                                                =
                                                                let uu____15427
                                                                  =
                                                                  let uu____15430
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15430
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15427
                                                                 in
                                                              (name, univs1,
                                                                uu____15424,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15409
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15408;
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
                                                          uu____15407)
                                                         in
                                                      (name, uu____15386)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____15185
                                         in
                                      (match uu____15156 with
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
                             | uu____15669 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15801  ->
                             match uu____15801 with
                             | (name_doc,uu____15829,uu____15830) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15910  ->
                             match uu____15910 with
                             | (uu____15931,uu____15932,se) -> se))
                      in
                   let uu____15962 =
                     let uu____15969 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____15969 rng
                      in
                   (match uu____15962 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____16035  ->
                                  match uu____16035 with
                                  | (uu____16058,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____16109,tps,k,uu____16112,constrs)
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
                                  | uu____16131 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____16148  ->
                                 match uu____16148 with
                                 | (lid,doc1) ->
                                     FStar_ToSyntax_Env.push_doc env4 lid
                                       doc1) env4 name_docs
                           in
                        (env5,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
  
let (desugar_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.binder Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binders  ->
      let uu____16183 =
        FStar_List.fold_left
          (fun uu____16206  ->
             fun b  ->
               match uu____16206 with
               | (env1,binders1) ->
                   let uu____16226 = desugar_binder env1 b  in
                   (match uu____16226 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16243 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____16243 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____16260 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____16183 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let (push_reflect_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lid -> FStar_Range.range -> FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun quals  ->
      fun effect_name  ->
        fun range  ->
          let uu____16305 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___106_16310  ->
                    match uu___106_16310 with
                    | FStar_Syntax_Syntax.Reflectable uu____16311 -> true
                    | uu____16312 -> false))
             in
          if uu____16305
          then
            let monad_env =
              FStar_ToSyntax_Env.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              FStar_All.pipe_right (FStar_Ident.id_of_text "reflect")
                (FStar_ToSyntax_Env.qualify monad_env)
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
            FStar_ToSyntax_Env.push_sigelt env refl_decl
          else env
  
let rec (desugar_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                let env0 = env  in
                let monad_env =
                  FStar_ToSyntax_Env.enter_monad_scope env eff_name  in
                let uu____16411 = desugar_binders monad_env eff_binders  in
                match uu____16411 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____16432 =
                        let uu____16433 =
                          let uu____16440 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          FStar_Pervasives_Native.fst uu____16440  in
                        FStar_List.length uu____16433  in
                      uu____16432 = (Prims.parse_int "1")  in
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
                          (uu____16482,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16484,uu____16485,uu____16486),uu____16487)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16520 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____16521 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16533 = name_of_eff_decl decl  in
                           FStar_List.mem uu____16533 mandatory_members)
                        eff_decls
                       in
                    (match uu____16521 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16550 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16579  ->
                                   fun decl  ->
                                     match uu____16579 with
                                     | (env2,out) ->
                                         let uu____16599 =
                                           desugar_decl env2 decl  in
                                         (match uu____16599 with
                                          | (env3,ses) ->
                                              let uu____16612 =
                                                let uu____16615 =
                                                  FStar_List.hd ses  in
                                                uu____16615 :: out  in
                                              (env3, uu____16612)))
                                (env1, []))
                            in
                         (match uu____16550 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16683,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16686,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16687,
                                                                (def,uu____16689)::
                                                                (cps_type,uu____16691)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16692;
                                                             FStar_Parser_AST.level
                                                               = uu____16693;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16745 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16745 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16765 =
                                                   let uu____16766 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____16767 =
                                                     let uu____16768 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16768
                                                      in
                                                   let uu____16773 =
                                                     let uu____16774 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16774
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16766;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16767;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16773
                                                   }  in
                                                 (uu____16765, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16781,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16784,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16819 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16819 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16839 =
                                                   let uu____16840 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____16841 =
                                                     let uu____16842 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16842
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16840;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16841;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____16839, doc1))
                                        | uu____16849 ->
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
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange)))
                                   in
                                let uu____16879 =
                                  let uu____16880 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16880
                                   in
                                ([], uu____16879)  in
                              let mname =
                                FStar_ToSyntax_Env.qualify env0 eff_name  in
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
                                    let uu____16897 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____16897)  in
                                  let uu____16904 =
                                    let uu____16905 =
                                      let uu____16906 =
                                        let uu____16907 = lookup "repr"  in
                                        FStar_Pervasives_Native.snd
                                          uu____16907
                                         in
                                      let uu____16916 = lookup "return"  in
                                      let uu____16917 = lookup "bind"  in
                                      {
                                        FStar_Syntax_Syntax.cattributes = [];
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
                                          uu____16906;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16916;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16917;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16905
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16904;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = []
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___107_16921  ->
                                          match uu___107_16921 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16922 -> true
                                          | uu____16923 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____16933 =
                                     let uu____16934 =
                                       let uu____16935 = lookup "return_wp"
                                          in
                                       let uu____16936 = lookup "bind_wp"  in
                                       let uu____16937 =
                                         lookup "if_then_else"  in
                                       let uu____16938 = lookup "ite_wp"  in
                                       let uu____16939 = lookup "stronger"
                                          in
                                       let uu____16940 = lookup "close_wp"
                                          in
                                       let uu____16941 = lookup "assert_p"
                                          in
                                       let uu____16942 = lookup "assume_p"
                                          in
                                       let uu____16943 = lookup "null_wp"  in
                                       let uu____16944 = lookup "trivial"  in
                                       let uu____16945 =
                                         if rr
                                         then
                                           let uu____16946 = lookup "repr"
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16946
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____16962 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____16964 =
                                         if rr then lookup "bind" else un_ts
                                          in
                                       {
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____16935;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16936;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16937;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16938;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16939;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16940;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16941;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16942;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16943;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16944;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16945;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____16962;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____16964;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16934
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16933;
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
                                FStar_ToSyntax_Env.push_sigelt env0 se  in
                              let env4 =
                                FStar_ToSyntax_Env.push_doc env3 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              let env5 =
                                FStar_All.pipe_right actions_docs
                                  (FStar_List.fold_left
                                     (fun env5  ->
                                        fun uu____16989  ->
                                          match uu____16989 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____17003 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____17003
                                                 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4)
                                 in
                              let env6 =
                                push_reflect_effect env5 qualifiers mname
                                  d.FStar_Parser_AST.drange
                                 in
                              let env7 =
                                FStar_ToSyntax_Env.push_doc env6 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              (env7, [se])))

and (desugar_redefine_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelt Prims.list)
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
                let env1 = FStar_ToSyntax_Env.enter_monad_scope env eff_name
                   in
                let uu____17027 = desugar_binders env1 eff_binders  in
                match uu____17027 with
                | (env2,binders) ->
                    let uu____17046 =
                      let uu____17065 = head_and_args defn  in
                      match uu____17065 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____17110 ->
                                let uu____17111 =
                                  let uu____17116 =
                                    let uu____17117 =
                                      let uu____17118 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____17118 " not found"
                                       in
                                    Prims.strcat "Effect " uu____17117  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____17116)
                                   in
                                FStar_Errors.raise_error uu____17111
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____17120 =
                            match FStar_List.rev args with
                            | (last_arg,uu____17150)::args_rev ->
                                (match last_arg.FStar_Parser_AST.tm with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____17189 -> ([], args))
                            | uu____17198 -> ([], args)  in
                          (match uu____17120 with
                           | (cattributes,args1) ->
                               let uu____17249 = desugar_args env2 args1  in
                               let uu____17258 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____17249, uu____17258))
                       in
                    (match uu____17046 with
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
                          (let uu____17314 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____17314 with
                           | (ed_binders,uu____17328,ed_binders_opening) ->
                               let sub1 uu____17339 =
                                 match uu____17339 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____17353 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____17353 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____17357 =
                                       let uu____17358 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____17358)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____17357
                                  in
                               let mname =
                                 FStar_ToSyntax_Env.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____17363 =
                                   let uu____17364 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____17364
                                    in
                                 let uu____17375 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____17376 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____17377 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____17378 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____17379 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____17380 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____17381 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____17382 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____17383 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____17384 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____17385 =
                                   let uu____17386 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____17386
                                    in
                                 let uu____17397 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____17398 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____17399 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____17407 =
                                          FStar_ToSyntax_Env.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____17408 =
                                          let uu____17409 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17409
                                           in
                                        let uu____17420 =
                                          let uu____17421 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17421
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____17407;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____17408;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____17420
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
                                     uu____17363;
                                   FStar_Syntax_Syntax.ret_wp = uu____17375;
                                   FStar_Syntax_Syntax.bind_wp = uu____17376;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____17377;
                                   FStar_Syntax_Syntax.ite_wp = uu____17378;
                                   FStar_Syntax_Syntax.stronger = uu____17379;
                                   FStar_Syntax_Syntax.close_wp = uu____17380;
                                   FStar_Syntax_Syntax.assert_p = uu____17381;
                                   FStar_Syntax_Syntax.assume_p = uu____17382;
                                   FStar_Syntax_Syntax.null_wp = uu____17383;
                                   FStar_Syntax_Syntax.trivial = uu____17384;
                                   FStar_Syntax_Syntax.repr = uu____17385;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____17397;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____17398;
                                   FStar_Syntax_Syntax.actions = uu____17399
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____17434 =
                                     let uu____17435 =
                                       let uu____17442 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____17442
                                        in
                                     FStar_List.length uu____17435  in
                                   uu____17434 = (Prims.parse_int "1")  in
                                 let uu____17471 =
                                   let uu____17474 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____17474 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____17471;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = []
                                 }  in
                               let monad_env = env2  in
                               let env3 =
                                 FStar_ToSyntax_Env.push_sigelt env0 se  in
                               let env4 =
                                 FStar_ToSyntax_Env.push_doc env3 ed_lid
                                   d.FStar_Parser_AST.doc
                                  in
                               let env5 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env5  ->
                                         fun a  ->
                                           let doc1 =
                                             FStar_ToSyntax_Env.try_lookup_doc
                                               env5
                                               a.FStar_Syntax_Syntax.action_name
                                              in
                                           let env6 =
                                             let uu____17494 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                in
                                             FStar_ToSyntax_Env.push_sigelt
                                               env5 uu____17494
                                              in
                                           FStar_ToSyntax_Env.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____17496 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____17496
                                 then
                                   let reflect_lid =
                                     FStar_All.pipe_right
                                       (FStar_Ident.id_of_text "reflect")
                                       (FStar_ToSyntax_Env.qualify monad_env)
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
                                   FStar_ToSyntax_Env.push_sigelt env5
                                     refl_decl
                                 else env5  in
                               let env7 =
                                 FStar_ToSyntax_Env.push_doc env6 mname
                                   d.FStar_Parser_AST.doc
                                  in
                               (env7, [se]))))

and (mk_comment_attr :
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun d  ->
    let uu____17511 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____17511 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____17562 ->
              let uu____17563 =
                let uu____17564 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____17564
                 in
              Prims.strcat "\n  " uu____17563
          | uu____17565 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____17578  ->
               match uu____17578 with
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
          let uu____17596 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____17596
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____17598 =
          let uu____17607 = FStar_Syntax_Syntax.as_arg arg  in [uu____17607]
           in
        FStar_Syntax_Util.mk_app fv uu____17598

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____17614 = desugar_decl_noattrs env d  in
      match uu____17614 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____17634 = mk_comment_attr d  in uu____17634 :: attrs1  in
          let s =
            FStar_List.fold_left
              (fun s  ->
                 fun a  ->
                   let uu____17645 =
                     let uu____17646 = FStar_Syntax_Print.term_to_string a
                        in
                     Prims.strcat "; " uu____17646  in
                   Prims.strcat s uu____17645) "" attrs2
             in
          let uu____17647 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___133_17653 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___133_17653.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___133_17653.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_17653.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_17653.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____17647)

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
      | FStar_Parser_AST.Fsdoc uu____17679 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17695 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____17695, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____17734  ->
                 match uu____17734 with | (x,uu____17742) -> x) tcs
             in
          let uu____17747 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____17747 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17769;
                    FStar_Parser_AST.prange = uu____17770;_},uu____17771)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17780;
                    FStar_Parser_AST.prange = uu____17781;_},uu____17782)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17797;
                         FStar_Parser_AST.prange = uu____17798;_},uu____17799);
                    FStar_Parser_AST.prange = uu____17800;_},uu____17801)::[]
                   -> false
               | (p,uu____17817)::[] ->
                   let uu____17826 = is_app_pattern p  in
                   Prims.op_Negation uu____17826
               | uu____17827 -> false)
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
            let ds_lets = desugar_term_maybe_top true env as_inner_let  in
            let uu____17901 =
              let uu____17902 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____17902.FStar_Syntax_Syntax.n  in
            (match uu____17901 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17910) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____17943::uu____17944 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____17947 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___108_17961  ->
                               match uu___108_17961 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____17964;
                                   FStar_Syntax_Syntax.lbunivs = uu____17965;
                                   FStar_Syntax_Syntax.lbtyp = uu____17966;
                                   FStar_Syntax_Syntax.lbeff = uu____17967;
                                   FStar_Syntax_Syntax.lbdef = uu____17968;
                                   FStar_Syntax_Syntax.lbattrs = uu____17969;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____17981;
                                   FStar_Syntax_Syntax.lbtyp = uu____17982;
                                   FStar_Syntax_Syntax.lbeff = uu____17983;
                                   FStar_Syntax_Syntax.lbdef = uu____17984;
                                   FStar_Syntax_Syntax.lbattrs = uu____17985;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____17999 =
                     FStar_All.pipe_right lets1
                       (FStar_Util.for_some
                          (fun uu____18030  ->
                             match uu____18030 with
                             | (uu____18043,(uu____18044,t)) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____17999
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____18068 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____18068
                   then
                     let uu____18077 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___134_18091 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___135_18093 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___135_18093.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___135_18093.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___134_18091.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___134_18091.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___134_18091.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___134_18091.FStar_Syntax_Syntax.lbdef);
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___134_18091.FStar_Syntax_Syntax.lbattrs)
                               }))
                        in
                     ((FStar_Pervasives_Native.fst lbs), uu____18077)
                   else lbs  in
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let attrs =
                   FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
                    in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = attrs
                   }  in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s  in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id1  ->
                          FStar_ToSyntax_Env.push_doc env2 id1
                            d.FStar_Parser_AST.doc) env1 names1
                    in
                 (env2, [s])
             | uu____18128 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____18134 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____18153 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____18134 with
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
                       let uu___136_18177 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___136_18177.FStar_Parser_AST.prange)
                       }
                   | uu____18178 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___137_18185 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___137_18185.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___137_18185.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___137_18185.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____18217 id1 =
                   match uu____18217 with
                   | (env1,ses) ->
                       let main =
                         let uu____18238 =
                           let uu____18239 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____18239  in
                         FStar_Parser_AST.mk_term uu____18238
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
                       let uu____18289 = desugar_decl env1 id_decl  in
                       (match uu____18289 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____18307 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____18307 FStar_Util.set_elements
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
          let lid = FStar_ToSyntax_Env.qualify env id1  in
          let env1 =
            FStar_ToSyntax_Env.push_doc env lid d.FStar_Parser_AST.doc  in
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
            let uu____18338 = close_fun env t  in
            desugar_term env uu____18338  in
          let quals1 =
            let uu____18342 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env)
               in
            if uu____18342
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_ToSyntax_Env.qualify env id1  in
          let se =
            let uu____18348 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____18348;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____18360 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____18360 with
           | (t,uu____18374) ->
               let l = FStar_ToSyntax_Env.qualify env id1  in
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
               let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
               let env2 =
                 FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc
                  in
               let data_ops = mk_data_projector_names [] env2 se  in
               let discs = mk_data_discriminators [] env2 [l]  in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops)
                  in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____18408 =
              let uu____18415 = FStar_Syntax_Syntax.null_binder t  in
              [uu____18415]  in
            let uu____18416 =
              let uu____18419 =
                let uu____18420 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____18420  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____18419
               in
            FStar_Syntax_Util.arrow uu____18408 uu____18416  in
          let l = FStar_ToSyntax_Env.qualify env id1  in
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
          let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 se  in
          let discs = mk_data_discriminators [] env2 [l]  in
          let env3 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
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
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
      | FStar_Parser_AST.SubEffect l ->
          let lookup l1 =
            let uu____18482 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____18482 with
            | FStar_Pervasives_Native.None  ->
                let uu____18485 =
                  let uu____18490 =
                    let uu____18491 =
                      let uu____18492 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____18492 " not found"  in
                    Prims.strcat "Effect name " uu____18491  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____18490)  in
                FStar_Errors.raise_error uu____18485
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____18496 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18538 =
                  let uu____18547 =
                    let uu____18554 = desugar_term env t  in
                    ([], uu____18554)  in
                  FStar_Pervasives_Native.Some uu____18547  in
                (uu____18538, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18587 =
                  let uu____18596 =
                    let uu____18603 = desugar_term env wp  in
                    ([], uu____18603)  in
                  FStar_Pervasives_Native.Some uu____18596  in
                let uu____18612 =
                  let uu____18621 =
                    let uu____18628 = desugar_term env t  in
                    ([], uu____18628)  in
                  FStar_Pervasives_Native.Some uu____18621  in
                (uu____18587, uu____18612)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18654 =
                  let uu____18663 =
                    let uu____18670 = desugar_term env t  in
                    ([], uu____18670)  in
                  FStar_Pervasives_Native.Some uu____18663  in
                (FStar_Pervasives_Native.None, uu____18654)
             in
          (match uu____18496 with
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

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t,FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun decls  ->
      let uu____18758 =
        FStar_List.fold_left
          (fun uu____18778  ->
             fun d  ->
               match uu____18778 with
               | (env1,sigelts) ->
                   let uu____18798 = desugar_decl env1 d  in
                   (match uu____18798 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____18758 with
      | (env1,sigelts) ->
          let rec forward acc uu___110_18839 =
            match uu___110_18839 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18853,FStar_Syntax_Syntax.Sig_let uu____18854) ->
                     let uu____18867 =
                       let uu____18870 =
                         let uu___138_18871 = se2  in
                         let uu____18872 =
                           let uu____18875 =
                             FStar_List.filter
                               (fun uu___109_18889  ->
                                  match uu___109_18889 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____18893;
                                           FStar_Syntax_Syntax.vars =
                                             uu____18894;_},uu____18895);
                                      FStar_Syntax_Syntax.pos = uu____18896;
                                      FStar_Syntax_Syntax.vars = uu____18897;_}
                                      when
                                      let uu____18920 =
                                        let uu____18921 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____18921
                                         in
                                      uu____18920 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____18922 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____18875
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___138_18871.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___138_18871.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___138_18871.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___138_18871.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____18872
                         }  in
                       uu____18870 :: se1 :: acc  in
                     forward uu____18867 sigelts1
                 | uu____18927 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____18935 = forward [] sigelts  in (env1, uu____18935)
  
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
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul,Prims.bool)
          FStar_Pervasives_Native.tuple3)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____18986) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____18990;
               FStar_Syntax_Syntax.exports = uu____18991;
               FStar_Syntax_Syntax.is_interface = uu____18992;_},FStar_Parser_AST.Module
             (current_lid,uu____18994)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____19002) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____19005 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____19041 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname FStar_ToSyntax_Env.default_mii
                 in
              (uu____19041, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____19058 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname FStar_ToSyntax_Env.default_mii
                 in
              (uu____19058, mname, decls, false)
           in
        match uu____19005 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____19088 = desugar_decls env2 decls  in
            (match uu____19088 with
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
          let uu____19142 =
            (FStar_Options.interactive ()) &&
              (let uu____19144 =
                 let uu____19145 =
                   let uu____19146 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____19146  in
                 FStar_Util.get_file_extension uu____19145  in
               FStar_List.mem uu____19144 ["fsti"; "fsi"])
             in
          if uu____19142 then as_interface m else m  in
        let uu____19150 = desugar_modul_common curmod env m1  in
        match uu____19150 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____19165 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____19181 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____19181 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____19197 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____19197
            then
              let uu____19198 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____19198
            else ());
           (let uu____19200 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____19200, modul)))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____19214 = desugar_modul env modul  in
      match uu____19214 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____19241 = desugar_decls env decls  in
      match uu____19241 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____19279 = desugar_partial_modul modul env a_modul  in
        match uu____19279 with | (env1,modul1) -> (modul1, env1)
  
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        Prims.unit FStar_ToSyntax_Env.withenv)
  =
  fun m  ->
    fun mii  ->
      fun erase_univs  ->
        fun en  ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____19353 ->
                  let t =
                    let uu____19361 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____19361  in
                  let uu____19370 =
                    let uu____19371 = FStar_Syntax_Subst.compress t  in
                    uu____19371.FStar_Syntax_Syntax.n  in
                  (match uu____19370 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____19381,uu____19382)
                       -> bs1
                   | uu____19403 -> failwith "Impossible")
               in
            let uu____19410 =
              let uu____19417 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____19417
                FStar_Syntax_Syntax.t_unit
               in
            match uu____19410 with
            | (binders,uu____19419,binders_opening) ->
                let erase_term t =
                  let uu____19425 =
                    let uu____19426 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____19426  in
                  FStar_Syntax_Subst.close binders uu____19425  in
                let erase_tscheme uu____19442 =
                  match uu____19442 with
                  | (us,t) ->
                      let t1 =
                        let uu____19462 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____19462 t  in
                      let uu____19465 =
                        let uu____19466 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____19466  in
                      ([], uu____19465)
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
                    | uu____19495 ->
                        let bs =
                          let uu____19503 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____19503  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____19533 =
                          let uu____19534 =
                            let uu____19537 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____19537  in
                          uu____19534.FStar_Syntax_Syntax.n  in
                        (match uu____19533 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____19545,uu____19546) -> bs1
                         | uu____19567 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____19578 =
                      let uu____19579 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____19579  in
                    FStar_Syntax_Subst.close binders uu____19578  in
                  let uu___139_19580 = action  in
                  let uu____19581 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____19582 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___139_19580.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___139_19580.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____19581;
                    FStar_Syntax_Syntax.action_typ = uu____19582
                  }  in
                let uu___140_19583 = ed  in
                let uu____19584 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____19585 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____19586 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____19587 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____19588 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____19589 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____19590 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____19591 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____19592 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____19593 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____19594 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____19595 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____19596 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____19597 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____19598 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____19599 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___140_19583.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___140_19583.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____19584;
                  FStar_Syntax_Syntax.signature = uu____19585;
                  FStar_Syntax_Syntax.ret_wp = uu____19586;
                  FStar_Syntax_Syntax.bind_wp = uu____19587;
                  FStar_Syntax_Syntax.if_then_else = uu____19588;
                  FStar_Syntax_Syntax.ite_wp = uu____19589;
                  FStar_Syntax_Syntax.stronger = uu____19590;
                  FStar_Syntax_Syntax.close_wp = uu____19591;
                  FStar_Syntax_Syntax.assert_p = uu____19592;
                  FStar_Syntax_Syntax.assume_p = uu____19593;
                  FStar_Syntax_Syntax.null_wp = uu____19594;
                  FStar_Syntax_Syntax.trivial = uu____19595;
                  FStar_Syntax_Syntax.repr = uu____19596;
                  FStar_Syntax_Syntax.return_repr = uu____19597;
                  FStar_Syntax_Syntax.bind_repr = uu____19598;
                  FStar_Syntax_Syntax.actions = uu____19599
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___141_19611 = se  in
                  let uu____19612 =
                    let uu____19613 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____19613  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19612;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___141_19611.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___141_19611.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___141_19611.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___141_19611.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___142_19617 = se  in
                  let uu____19618 =
                    let uu____19619 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19619
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19618;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___142_19617.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___142_19617.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___142_19617.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___142_19617.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____19621 -> FStar_ToSyntax_Env.push_sigelt env se  in
          let uu____19622 =
            FStar_ToSyntax_Env.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____19622 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____19634 =
                  FStar_ToSyntax_Env.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____19634
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_ToSyntax_Env.finish en2 m  in
              let uu____19636 =
                if pop_when_done
                then
                  FStar_ToSyntax_Env.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____19636)
  