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
      | FStar_Parser_AST.Assign (uu____447,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____450) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____456) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____461,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____476,ts) ->
          FStar_List.collect
            (fun uu____497  ->
               match uu____497 with | (t1,uu____505) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____506,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____514) ->
          let uu____515 = free_type_vars env t1  in
          let uu____518 = free_type_vars env t2  in
          FStar_List.append uu____515 uu____518
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____523 = free_type_vars_b env b  in
          (match uu____523 with
           | (env1,f) ->
               let uu____538 = free_type_vars env1 t1  in
               FStar_List.append f uu____538)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____547 =
            FStar_List.fold_left
              (fun uu____567  ->
                 fun binder  ->
                   match uu____567 with
                   | (env1,free) ->
                       let uu____587 = free_type_vars_b env1 binder  in
                       (match uu____587 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____547 with
           | (env1,free) ->
               let uu____618 = free_type_vars env1 body  in
               FStar_List.append free uu____618)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____627 =
            FStar_List.fold_left
              (fun uu____647  ->
                 fun binder  ->
                   match uu____647 with
                   | (env1,free) ->
                       let uu____667 = free_type_vars_b env1 binder  in
                       (match uu____667 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____627 with
           | (env1,free) ->
               let uu____698 = free_type_vars env1 body  in
               FStar_List.append free uu____698)
      | FStar_Parser_AST.Project (t1,uu____702) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____706 -> []
      | FStar_Parser_AST.Let uu____713 -> []
      | FStar_Parser_AST.LetOpen uu____734 -> []
      | FStar_Parser_AST.If uu____739 -> []
      | FStar_Parser_AST.QForall uu____746 -> []
      | FStar_Parser_AST.QExists uu____759 -> []
      | FStar_Parser_AST.Record uu____772 -> []
      | FStar_Parser_AST.Match uu____785 -> []
      | FStar_Parser_AST.TryWith uu____800 -> []
      | FStar_Parser_AST.Bind uu____815 -> []
      | FStar_Parser_AST.Seq uu____822 -> []

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
      | uu____910 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____930 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____930  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____948 =
                     let uu____949 =
                       let uu____954 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____954)  in
                     FStar_Parser_AST.TAnnotated uu____949  in
                   FStar_Parser_AST.mk_binder uu____948 x.FStar_Ident.idRange
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
        let uu____967 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____967  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____985 =
                     let uu____986 =
                       let uu____991 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____991)  in
                     FStar_Parser_AST.TAnnotated uu____986  in
                   FStar_Parser_AST.mk_binder uu____985 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Product uu____993 -> t
           | uu____1000 ->
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
      | uu____1032 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1038,uu____1039) -> true
    | FStar_Parser_AST.PatVar (uu____1044,uu____1045) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1051) -> is_var_pattern p1
    | uu____1052 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1057) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1058;
           FStar_Parser_AST.prange = uu____1059;_},uu____1060)
        -> true
    | uu____1071 -> false
  
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
    | uu____1075 -> p
  
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
            let uu____1115 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1115 with
             | (name,args,uu____1146) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1172);
               FStar_Parser_AST.prange = uu____1173;_},args)
            when is_top_level1 ->
            let uu____1183 =
              let uu____1188 = FStar_ToSyntax_Env.qualify env id1  in
              FStar_Util.Inr uu____1188  in
            (uu____1183, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1198);
               FStar_Parser_AST.prange = uu____1199;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1217 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1255 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1256,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1259 -> acc
      | FStar_Parser_AST.PatTvar uu____1260 -> acc
      | FStar_Parser_AST.PatOp uu____1267 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1275) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1284) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1299 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1299
      | FStar_Parser_AST.PatAscribed (pat,uu____1307) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1345 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1373 -> false
  
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
  fun uu___86_1399  ->
    match uu___86_1399 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1406 -> failwith "Impossible"
  
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
      fun uu___87_1431  ->
        match uu___87_1431 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1447 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1447, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1452 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____1452 with
             | (env1,a1) ->
                 (((let uu___111_1472 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___111_1472.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___111_1472.FStar_Syntax_Syntax.index);
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
  fun uu____1497  ->
    match uu____1497 with
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
      let uu____1562 =
        let uu____1577 =
          let uu____1578 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1578  in
        let uu____1579 =
          let uu____1588 =
            let uu____1595 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1595)  in
          [uu____1588]  in
        (uu____1577, uu____1579)  in
      FStar_Syntax_Syntax.Tm_app uu____1562  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1628 =
        let uu____1643 =
          let uu____1644 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1644  in
        let uu____1645 =
          let uu____1654 =
            let uu____1661 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1661)  in
          [uu____1654]  in
        (uu____1643, uu____1645)  in
      FStar_Syntax_Syntax.Tm_app uu____1628  in
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
          let uu____1704 =
            let uu____1719 =
              let uu____1720 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____1720  in
            let uu____1721 =
              let uu____1730 =
                let uu____1737 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____1737)  in
              let uu____1740 =
                let uu____1749 =
                  let uu____1756 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____1756)  in
                [uu____1749]  in
              uu____1730 :: uu____1740  in
            (uu____1719, uu____1721)  in
          FStar_Syntax_Syntax.Tm_app uu____1704  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___88_1787  ->
    match uu___88_1787 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1788 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1796 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1796)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  ->
        let uu____1811 =
          let uu____1812 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____1812  in
        FStar_Util.Inr uu____1811
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1823)) ->
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
             let uu____1889 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1889
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1900 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1900
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1911 =
               let uu____1916 =
                 let uu____1917 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____1917
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____1916)
                in
             FStar_Errors.raise_error uu____1911 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____1922 ->
        let rec aux t1 univargs =
          match t1.FStar_Parser_AST.tm with
          | FStar_Parser_AST.App (t2,targ,uu____1958) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___89_1982  ->
                     match uu___89_1982 with
                     | FStar_Util.Inr uu____1987 -> true
                     | uu____1988 -> false) univargs
              then
                let uu____1993 =
                  let uu____1994 =
                    FStar_List.map
                      (fun uu___90_2003  ->
                         match uu___90_2003 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____1994  in
                FStar_Util.Inr uu____1993
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___91_2020  ->
                        match uu___91_2020 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2026 -> failwith "impossible")
                     univargs
                    in
                 let uu____2027 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2027)
          | uu____2033 ->
              let uu____2034 =
                let uu____2039 =
                  let uu____2040 =
                    let uu____2041 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2041 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2040  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2039)  in
              FStar_Errors.raise_error uu____2034 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2050 ->
        let uu____2051 =
          let uu____2056 =
            let uu____2057 =
              let uu____2058 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2058 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2057  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2056)  in
        FStar_Errors.raise_error uu____2051 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields :
  'Auu____2077 .
    FStar_ToSyntax_Env.env ->
      (FStar_Ident.lident,'Auu____2077) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_ToSyntax_Env.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2102 = FStar_List.hd fields  in
        match uu____2102 with
        | (f,uu____2112) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2122 =
                match uu____2122 with
                | (f',uu____2128) ->
                    (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
                     (let uu____2130 =
                        FStar_ToSyntax_Env.belongs_to_record env f' record
                         in
                      if uu____2130
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
              (let uu____2134 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2134);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2351 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2358 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2359 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2361,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2402  ->
                          match uu____2402 with
                          | (p3,uu____2412) ->
                              let uu____2413 =
                                let uu____2414 =
                                  let uu____2417 = pat_vars p3  in
                                  FStar_Util.set_intersect uu____2417 out  in
                                FStar_Util.set_is_empty uu____2414  in
                              if uu____2413
                              then
                                let uu____2422 = pat_vars p3  in
                                FStar_Util.set_union out uu____2422
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                                    "Non-linear patterns are not permitted.")
                                  r) FStar_Syntax_Syntax.no_names)
             in
          pat_vars p1  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2429) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2430) -> ()
         | (true ,uu____2437) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____2472 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2472 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2486 ->
               let uu____2489 = push_bv_maybe_mut e x  in
               (match uu____2489 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2576 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2592 =
                 let uu____2593 =
                   let uu____2594 =
                     let uu____2601 =
                       let uu____2602 =
                         let uu____2607 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2607, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2602  in
                     (uu____2601, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2594  in
                 {
                   FStar_Parser_AST.pat = uu____2593;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2592
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2612 = aux loc env1 p2  in
               (match uu____2612 with
                | (loc1,env',binder,p3,imp) ->
                    let annot_pat_var p4 t1 =
                      match p4.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let uu___112_2666 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var
                                 (let uu___113_2671 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___113_2671.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___113_2671.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___112_2666.FStar_Syntax_Syntax.p)
                          }
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let uu___114_2673 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild
                                 (let uu___115_2678 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___115_2678.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___115_2678.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___114_2673.FStar_Syntax_Syntax.p)
                          }
                      | uu____2679 when top -> p4
                      | uu____2680 ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                              "Type ascriptions within patterns are only allowed on variables")
                            orig.FStar_Parser_AST.prange
                       in
                    let uu____2683 =
                      match binder with
                      | LetBinder uu____2696 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2710 = close_fun env1 t  in
                            desugar_term env1 uu____2710  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2712 -> true)
                           then
                             (let uu____2713 =
                                let uu____2718 =
                                  let uu____2719 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____2720 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____2721 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3
                                    "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                    uu____2719 uu____2720 uu____2721
                                   in
                                (FStar_Errors.Warning_MultipleAscriptions,
                                  uu____2718)
                                 in
                              FStar_Errors.log_issue
                                orig.FStar_Parser_AST.prange uu____2713)
                           else ();
                           (let uu____2723 = annot_pat_var p3 t1  in
                            (uu____2723,
                              (LocalBinder
                                 ((let uu___116_2729 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___116_2729.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___116_2729.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }), aq)))))
                       in
                    (match uu____2683 with
                     | (p4,binder1) -> (loc1, env', binder1, p4, imp)))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2751 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2751, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2762 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2762, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2783 = resolvex loc env1 x  in
               (match uu____2783 with
                | (loc1,env2,xbv) ->
                    let uu____2805 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2805, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2826 = resolvex loc env1 x  in
               (match uu____2826 with
                | (loc1,env2,xbv) ->
                    let uu____2848 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2848, imp))
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
               let uu____2860 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2860, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2884;_},args)
               ->
               let uu____2890 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2931  ->
                        match uu____2931 with
                        | (loc1,env2,args1) ->
                            let uu____2979 = aux loc1 env2 arg  in
                            (match uu____2979 with
                             | (loc2,env3,uu____3008,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____2890 with
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
                    let uu____3078 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3078, false))
           | FStar_Parser_AST.PatApp uu____3095 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3117 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3150  ->
                        match uu____3150 with
                        | (loc1,env2,pats1) ->
                            let uu____3182 = aux loc1 env2 pat  in
                            (match uu____3182 with
                             | (loc2,env3,uu____3207,pat1,uu____3209) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3117 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3252 =
                        let uu____3255 =
                          let uu____3260 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3260  in
                        let uu____3261 =
                          let uu____3262 =
                            let uu____3275 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3275, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3262  in
                        FStar_All.pipe_left uu____3255 uu____3261  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3307 =
                               let uu____3308 =
                                 let uu____3321 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3321, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3308  in
                             FStar_All.pipe_left (pos_r r) uu____3307) pats1
                        uu____3252
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
               let uu____3365 =
                 FStar_List.fold_left
                   (fun uu____3405  ->
                      fun p2  ->
                        match uu____3405 with
                        | (loc1,env2,pats) ->
                            let uu____3454 = aux loc1 env2 p2  in
                            (match uu____3454 with
                             | (loc2,env3,uu____3483,pat,uu____3485) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3365 with
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
                    let uu____3580 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____3580 with
                     | (constr,uu____3602) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3605 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3607 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3607, false)))
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
                      (fun uu____3678  ->
                         match uu____3678 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3708  ->
                         match uu____3708 with
                         | (f,uu____3714) ->
                             let uu____3715 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3741  ->
                                       match uu____3741 with
                                       | (g,uu____3747) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____3715 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3752,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____3759 =
                   let uu____3760 =
                     let uu____3767 =
                       let uu____3768 =
                         let uu____3769 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____3769  in
                       FStar_Parser_AST.mk_pattern uu____3768
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____3767, args)  in
                   FStar_Parser_AST.PatApp uu____3760  in
                 FStar_Parser_AST.mk_pattern uu____3759
                   p1.FStar_Parser_AST.prange
                  in
               let uu____3772 = aux loc env1 app  in
               (match uu____3772 with
                | (env2,e,b,p2,uu____3801) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3829 =
                            let uu____3830 =
                              let uu____3843 =
                                let uu___117_3844 = fv  in
                                let uu____3845 =
                                  let uu____3848 =
                                    let uu____3849 =
                                      let uu____3856 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____3856)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3849
                                     in
                                  FStar_Pervasives_Native.Some uu____3848  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___117_3844.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___117_3844.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3845
                                }  in
                              (uu____3843, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____3830  in
                          FStar_All.pipe_left pos uu____3829
                      | uu____3883 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____3933 = aux' true loc env1 p2  in
               (match uu____3933 with
                | (loc1,env2,var,p3,uu____3960) ->
                    let uu____3965 =
                      FStar_List.fold_left
                        (fun uu____3997  ->
                           fun p4  ->
                             match uu____3997 with
                             | (loc2,env3,ps1) ->
                                 let uu____4030 = aux' true loc2 env3 p4  in
                                 (match uu____4030 with
                                  | (loc3,env4,uu____4055,p5,uu____4057) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____3965 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4108 ->
               let uu____4109 = aux' true loc env1 p1  in
               (match uu____4109 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4149 = aux_maybe_or env p  in
         match uu____4149 with
         | (env1,b,pats) ->
             ((let uu____4180 =
                 FStar_List.map
                   (fun pats1  ->
                      check_linear_pattern_variables pats1
                        p.FStar_Parser_AST.prange) pats
                  in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4180);
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
            let uu____4217 =
              let uu____4218 =
                let uu____4223 = FStar_ToSyntax_Env.qualify env x  in
                (uu____4223, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____4218  in
            (env, uu____4217, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4243 =
                  let uu____4244 =
                    let uu____4249 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4249, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4244  in
                mklet uu____4243
            | FStar_Parser_AST.PatVar (x,uu____4251) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4257);
                   FStar_Parser_AST.prange = uu____4258;_},t)
                ->
                let uu____4264 =
                  let uu____4265 =
                    let uu____4270 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____4271 = desugar_term env t  in
                    (uu____4270, uu____4271)  in
                  LetBinder uu____4265  in
                (env, uu____4264, [])
            | uu____4274 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4284 = desugar_data_pat env p is_mut  in
             match uu____4284 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4313;
                       FStar_Syntax_Syntax.p = uu____4314;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4319;
                       FStar_Syntax_Syntax.p = uu____4320;_}::[] -> []
                   | uu____4325 -> p1  in
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
  fun uu____4332  ->
    fun env  ->
      fun pat  ->
        let uu____4335 = desugar_data_pat env pat false  in
        match uu____4335 with | (env1,uu____4351,pat1) -> (env1, pat1)

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
      fun uu____4369  ->
        fun range  ->
          match uu____4369 with
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
              ((let uu____4379 =
                  let uu____4380 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4380  in
                if uu____4379
                then
                  let uu____4381 =
                    let uu____4386 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4386)  in
                  FStar_Errors.log_issue range uu____4381
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
                  let uu____4394 = FStar_ToSyntax_Env.try_lookup_lid env lid
                     in
                  match uu____4394 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4404) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             FStar_Ident.lid_of_path
                               (FStar_Ident.path_of_text private_intro_nm)
                               range
                              in
                           let private_fv =
                             let uu____4414 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4414 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___118_4415 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___118_4415.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___118_4415.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4416 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4423 =
                        let uu____4428 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4428)
                         in
                      FStar_Errors.raise_error uu____4423 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4444 =
                  let uu____4447 =
                    let uu____4448 =
                      let uu____4463 =
                        let uu____4472 =
                          let uu____4479 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4479)  in
                        [uu____4472]  in
                      (lid1, uu____4463)  in
                    FStar_Syntax_Syntax.Tm_app uu____4448  in
                  FStar_Syntax_Syntax.mk uu____4447  in
                uu____4444 FStar_Pervasives_Native.None range))

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
            let uu____4518 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid_with_attributes
                  else
                    FStar_ToSyntax_Env.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4518 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____4564;
                              FStar_Syntax_Syntax.vars = uu____4565;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____4588 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4588 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____4596 =
                                 let uu____4597 =
                                   let uu____4600 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____4600  in
                                 uu____4597.FStar_Syntax_Syntax.n  in
                               match uu____4596 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____4616))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____4617 -> msg
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
                             let uu____4621 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4621 " is deprecated"  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____4622 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____4627 =
                      let uu____4628 =
                        let uu____4635 = mk_ref_read tm1  in
                        (uu____4635,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____4628  in
                    FStar_All.pipe_left mk1 uu____4627
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
            { FStar_Ident.ns = uu____4651; FStar_Ident.ident = uu____4652;
              FStar_Ident.nsstr = uu____4653; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4656 ->
            let uu____4657 =
              let uu____4662 =
                let uu____4663 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____4663  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____4662)  in
            FStar_Errors.raise_error uu____4657 t.FStar_Parser_AST.range
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
          let uu___119_4683 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___119_4683.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___119_4683.FStar_Syntax_Syntax.vars)
          }  in
        match top.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4686 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____4737::uu____4738::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4742 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____4742 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4755;_},t1::t2::[])
                  ->
                  let uu____4760 = flatten1 t1  in
                  FStar_List.append uu____4760 [t2]
              | uu____4763 -> [t]  in
            let targs =
              let uu____4767 = flatten1 top  in
              FStar_All.pipe_right uu____4767
                (FStar_List.map
                   (fun t  ->
                      let uu____4777 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____4777))
               in
            let uu____4778 =
              let uu____4783 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4783
               in
            (match uu____4778 with
             | (tup,uu____4789) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4793 =
              let uu____4796 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              FStar_Pervasives_Native.fst uu____4796  in
            FStar_All.pipe_left setpos uu____4793
        | FStar_Parser_AST.Uvar u ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedUniverseVariable,
                (Prims.strcat "Unexpected universe variable "
                   (Prims.strcat (FStar_Ident.text_of_id u)
                      " in non-universe context")))
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4816 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____4816 with
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
                             let uu____4848 = desugar_term env t  in
                             (uu____4848, FStar_Pervasives_Native.None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4862)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4877 =
              let uu___120_4878 = top  in
              let uu____4879 =
                let uu____4880 =
                  let uu____4887 =
                    let uu___121_4888 = top  in
                    let uu____4889 =
                      let uu____4890 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4890  in
                    {
                      FStar_Parser_AST.tm = uu____4889;
                      FStar_Parser_AST.range =
                        (uu___121_4888.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___121_4888.FStar_Parser_AST.level)
                    }  in
                  (uu____4887, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4880  in
              {
                FStar_Parser_AST.tm = uu____4879;
                FStar_Parser_AST.range =
                  (uu___120_4878.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___120_4878.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4877
        | FStar_Parser_AST.Construct (n1,(a,uu____4893)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____4909 =
                let uu___122_4910 = top  in
                let uu____4911 =
                  let uu____4912 =
                    let uu____4919 =
                      let uu___123_4920 = top  in
                      let uu____4921 =
                        let uu____4922 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____4922  in
                      {
                        FStar_Parser_AST.tm = uu____4921;
                        FStar_Parser_AST.range =
                          (uu___123_4920.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___123_4920.FStar_Parser_AST.level)
                      }  in
                    (uu____4919, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____4912  in
                {
                  FStar_Parser_AST.tm = uu____4911;
                  FStar_Parser_AST.range =
                    (uu___122_4910.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___122_4910.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____4909))
        | FStar_Parser_AST.Construct (n1,(a,uu____4925)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4940 =
              let uu___124_4941 = top  in
              let uu____4942 =
                let uu____4943 =
                  let uu____4950 =
                    let uu___125_4951 = top  in
                    let uu____4952 =
                      let uu____4953 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4953  in
                    {
                      FStar_Parser_AST.tm = uu____4952;
                      FStar_Parser_AST.range =
                        (uu___125_4951.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___125_4951.FStar_Parser_AST.level)
                    }  in
                  (uu____4950, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4943  in
              {
                FStar_Parser_AST.tm = uu____4942;
                FStar_Parser_AST.range =
                  (uu___124_4941.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___124_4941.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4940
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4954; FStar_Ident.ident = uu____4955;
              FStar_Ident.nsstr = uu____4956; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4959; FStar_Ident.ident = uu____4960;
              FStar_Ident.nsstr = uu____4961; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4964; FStar_Ident.ident = uu____4965;
               FStar_Ident.nsstr = uu____4966; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____4984 =
              let uu____4985 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____4985  in
            mk1 uu____4984
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4986; FStar_Ident.ident = uu____4987;
              FStar_Ident.nsstr = uu____4988; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4991; FStar_Ident.ident = uu____4992;
              FStar_Ident.nsstr = uu____4993; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4996; FStar_Ident.ident = uu____4997;
              FStar_Ident.nsstr = uu____4998; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5003;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5005 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
              match uu____5005 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____5010 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____5010))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____5014 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____5014 with
             | (t1,mut) ->
                 (if Prims.op_Negation mut
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssignToImmutableValues,
                        "Can only assign to mutable values")
                      top.FStar_Parser_AST.range
                  else ();
                  mk_ref_assign t1 t21 top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Var l ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Name l ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____5041 = FStar_ToSyntax_Env.try_lookup_datacon env l
                   in
                match uu____5041 with
                | FStar_Pervasives_Native.Some uu____5050 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5055 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l
                       in
                    (match uu____5055 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5069 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5082 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____5082
              | uu____5083 ->
                  let uu____5090 =
                    let uu____5095 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____5095)  in
                  FStar_Errors.raise_error uu____5090
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____5098 = FStar_ToSyntax_Env.try_lookup_datacon env lid
                 in
              match uu____5098 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5101 =
                    let uu____5106 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____5106)
                     in
                  FStar_Errors.raise_error uu____5101
                    top.FStar_Parser_AST.range
              | uu____5107 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____5126 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____5126 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____5130 =
                    let uu____5137 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                       in
                    (uu____5137, true)  in
                  (match uu____5130 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5152 ->
                            let uu____5159 =
                              FStar_Util.take
                                (fun uu____5183  ->
                                   match uu____5183 with
                                   | (uu____5188,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args
                               in
                            (match uu____5159 with
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
                                     (fun uu____5252  ->
                                        match uu____5252 with
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
                    let uu____5299 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l  in
                    match uu____5299 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____5306 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5313 =
              FStar_List.fold_left
                (fun uu____5358  ->
                   fun b  ->
                     match uu____5358 with
                     | (env1,tparams,typs) ->
                         let uu____5415 = desugar_binder env1 b  in
                         (match uu____5415 with
                          | (xopt,t1) ->
                              let uu____5444 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5453 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____5453)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____5444 with
                               | (env2,x) ->
                                   let uu____5473 =
                                     let uu____5476 =
                                       let uu____5479 =
                                         let uu____5480 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5480
                                          in
                                       [uu____5479]  in
                                     FStar_List.append typs uu____5476  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___126_5506 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___126_5506.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___126_5506.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5473)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____5313 with
             | (env1,uu____5530,targs) ->
                 let uu____5552 =
                   let uu____5557 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5557
                    in
                 (match uu____5552 with
                  | (tup,uu____5563) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5574 = uncurry binders t  in
            (match uu____5574 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___92_5606 =
                   match uu___92_5606 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____5620 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____5620
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____5642 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____5642 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5657 = desugar_binder env b  in
            (match uu____5657 with
             | (FStar_Pervasives_Native.None ,uu____5664) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5674 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____5674 with
                  | ((x,uu____5680),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____5687 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____5687))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____5707 =
              FStar_List.fold_left
                (fun uu____5727  ->
                   fun pat  ->
                     match uu____5727 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5753,t) ->
                              let uu____5755 =
                                let uu____5758 = free_type_vars env1 t  in
                                FStar_List.append uu____5758 ftvs  in
                              (env1, uu____5755)
                          | uu____5763 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____5707 with
             | (uu____5768,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____5780 =
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
                   FStar_List.append uu____5780 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___93_5821 =
                   match uu___93_5821 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5859 =
                                 let uu____5860 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____5860
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____5859 body1  in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1  in
                       let uu____5913 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____5913
                   | p::rest ->
                       let uu____5924 = desugar_binding_pat env1 p  in
                       (match uu____5924 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5948 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____5953 =
                              match b with
                              | LetBinder uu____5986 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____6036) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6072 =
                                          let uu____6077 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____6077, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____6072
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6113,uu____6114) ->
                                             let tup2 =
                                               let uu____6116 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6116
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6120 =
                                                 let uu____6123 =
                                                   let uu____6124 =
                                                     let uu____6139 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____6142 =
                                                       let uu____6145 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____6146 =
                                                         let uu____6149 =
                                                           let uu____6150 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6150
                                                            in
                                                         [uu____6149]  in
                                                       uu____6145 ::
                                                         uu____6146
                                                        in
                                                     (uu____6139, uu____6142)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6124
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6123
                                                  in
                                               uu____6120
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____6161 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6161
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6192,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6194,pats)) ->
                                             let tupn =
                                               let uu____6233 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6233
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6243 =
                                                 let uu____6244 =
                                                   let uu____6259 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____6262 =
                                                     let uu____6271 =
                                                       let uu____6280 =
                                                         let uu____6281 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6281
                                                          in
                                                       [uu____6280]  in
                                                     FStar_List.append args
                                                       uu____6271
                                                      in
                                                   (uu____6259, uu____6262)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6244
                                                  in
                                               mk1 uu____6243  in
                                             let p2 =
                                               let uu____6301 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6301
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6336 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____5953 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6403,uu____6404,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              match e.FStar_Parser_AST.tm with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____6423 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____6427 ->
            let rec aux args e =
              match e.FStar_Parser_AST.tm with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6471 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6471  in
                  aux (arg :: args) e1
              | uu____6484 ->
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
            let uu____6512 =
              FStar_ToSyntax_Env.resolve_to_fully_qualified_name env bind_lid
               in
            (match uu____6512 with
             | FStar_Pervasives_Native.Some flid when
                 FStar_Ident.lid_equals flid tac_bind_lid ->
                 let r =
                   FStar_Parser_AST.mk_term
                     (FStar_Parser_AST.Const
                        (FStar_Const.Const_range (t2.FStar_Parser_AST.range)))
                     t2.FStar_Parser_AST.range FStar_Parser_AST.Expr
                    in
                 let uu____6517 =
                   FStar_Parser_AST.mkExplicitApp bind1 [r; t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6517
             | uu____6518 ->
                 let uu____6521 =
                   FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6521)
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6524 =
              let uu____6525 =
                let uu____6532 =
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
                (uu____6532,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____6525  in
            mk1 uu____6524
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            let uu____6584 =
              let uu____6589 = FStar_ToSyntax_Env.expect_typ env1  in
              if uu____6589 then desugar_typ else desugar_term  in
            uu____6584 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____6632 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6757  ->
                        match uu____6757 with
                        | (attr_opt,(p,def)) ->
                            let uu____6809 = is_app_pattern p  in
                            if uu____6809
                            then
                              let uu____6834 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____6834, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6898 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____6898, def1)
                               | uu____6931 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____6963);
                                           FStar_Parser_AST.prange =
                                             uu____6964;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____6994 =
                                            let uu____7009 =
                                              let uu____7014 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7014  in
                                            (uu____7009, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____6994, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____7069) ->
                                        if top_level
                                        then
                                          let uu____7098 =
                                            let uu____7113 =
                                              let uu____7118 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7118  in
                                            (uu____7113, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____7098, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____7172 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____7197 =
                FStar_List.fold_left
                  (fun uu____7264  ->
                     fun uu____7265  ->
                       match (uu____7264, uu____7265) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____7361,uu____7362),uu____7363))
                           ->
                           let uu____7456 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7482 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____7482 with
                                  | (env2,xx) ->
                                      let uu____7501 =
                                        let uu____7504 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____7504 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____7501))
                             | FStar_Util.Inr l ->
                                 let uu____7512 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____7512, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____7456 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____7197 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____7644 =
                    match uu____7644 with
                    | (attrs_opt,(uu____7674,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7726 = is_comp_type env1 t  in
                                if uu____7726
                                then
                                  ((let uu____7728 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7738 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____7738))
                                       in
                                    match uu____7728 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____7741 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7743 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____7743))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____7741
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____7747 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7747 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7751 ->
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
                              let uu____7766 =
                                let uu____7767 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7767
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____7766
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
                  let uu____7821 =
                    let uu____7822 =
                      let uu____7835 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs1), uu____7835)  in
                    FStar_Syntax_Syntax.Tm_let uu____7822  in
                  FStar_All.pipe_left mk1 uu____7821
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
              let uu____7889 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____7889 with
              | (env1,binder,pat1) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____7916 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7916
                            FStar_Pervasives_Native.None
                           in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [mk_lb (attrs, (FStar_Util.Inr fv), t, t12)]),
                               body1))
                    | LocalBinder (x,uu____7936) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat1 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7939;
                              FStar_Syntax_Syntax.p = uu____7940;_}::[] ->
                              body1
                          | uu____7945 ->
                              let uu____7948 =
                                let uu____7951 =
                                  let uu____7952 =
                                    let uu____7975 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____7976 =
                                      desugar_disjunctive_pattern pat1
                                        FStar_Pervasives_Native.None body1
                                       in
                                    (uu____7975, uu____7976)  in
                                  FStar_Syntax_Syntax.Tm_match uu____7952  in
                                FStar_Syntax_Syntax.mk uu____7951  in
                              uu____7948 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range
                           in
                        let uu____7986 =
                          let uu____7987 =
                            let uu____8000 =
                              let uu____8001 =
                                let uu____8002 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____8002]  in
                              FStar_Syntax_Subst.close uu____8001 body2  in
                            ((false,
                               [mk_lb
                                  (attrs, (FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____8000)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____7987  in
                        FStar_All.pipe_left mk1 uu____7986
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
            let uu____8030 = FStar_List.hd lbs  in
            (match uu____8030 with
             | (attrs,(head_pat,defn)) ->
                 let uu____8070 = is_rec || (is_app_pattern head_pat)  in
                 if uu____8070
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____8079 =
                let uu____8080 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____8080  in
              mk1 uu____8079  in
            let uu____8081 =
              let uu____8082 =
                let uu____8105 =
                  let uu____8108 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____8108
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None)
                   in
                let uu____8129 =
                  let uu____8144 =
                    let uu____8157 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range
                       in
                    let uu____8160 = desugar_term env t2  in
                    (uu____8157, FStar_Pervasives_Native.None, uu____8160)
                     in
                  let uu____8169 =
                    let uu____8184 =
                      let uu____8197 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range
                         in
                      let uu____8200 = desugar_term env t3  in
                      (uu____8197, FStar_Pervasives_Native.None, uu____8200)
                       in
                    [uu____8184]  in
                  uu____8144 :: uu____8169  in
                (uu____8105, uu____8129)  in
              FStar_Syntax_Syntax.Tm_match uu____8082  in
            mk1 uu____8081
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
            let desugar_branch uu____8341 =
              match uu____8341 with
              | (pat,wopt,b) ->
                  let uu____8359 = desugar_match_pat env pat  in
                  (match uu____8359 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8380 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____8380
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____8382 =
              let uu____8383 =
                let uu____8406 = desugar_term env e  in
                let uu____8407 = FStar_List.collect desugar_branch branches
                   in
                (uu____8406, uu____8407)  in
              FStar_Syntax_Syntax.Tm_match uu____8383  in
            FStar_All.pipe_left mk1 uu____8382
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8436 = is_comp_type env t  in
              if uu____8436
              then
                let uu____8443 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____8443
              else
                (let uu____8449 = desugar_term env t  in
                 FStar_Util.Inl uu____8449)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____8455 =
              let uu____8456 =
                let uu____8483 = desugar_term env e  in
                (uu____8483, (annot, tac_opt1), FStar_Pervasives_Native.None)
                 in
              FStar_Syntax_Syntax.Tm_ascribed uu____8456  in
            FStar_All.pipe_left mk1 uu____8455
        | FStar_Parser_AST.Record (uu____8508,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____8545 = FStar_List.hd fields  in
              match uu____8545 with | (f,uu____8557) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8599  ->
                        match uu____8599 with
                        | (g,uu____8605) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____8611,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8625 =
                         let uu____8630 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____8630)
                          in
                       FStar_Errors.raise_error uu____8625
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
                  let uu____8638 =
                    let uu____8649 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8680  ->
                              match uu____8680 with
                              | (f,uu____8690) ->
                                  let uu____8691 =
                                    let uu____8692 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8692
                                     in
                                  (uu____8691, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____8649)  in
                  FStar_Parser_AST.Construct uu____8638
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____8710 =
                      let uu____8711 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____8711  in
                    FStar_Parser_AST.mk_term uu____8710 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____8713 =
                      let uu____8726 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8756  ->
                                match uu____8756 with
                                | (f,uu____8766) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____8726)  in
                    FStar_Parser_AST.Record uu____8713  in
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
                         FStar_Syntax_Syntax.pos = uu____8828;
                         FStar_Syntax_Syntax.vars = uu____8829;_},args);
                    FStar_Syntax_Syntax.pos = uu____8831;
                    FStar_Syntax_Syntax.vars = uu____8832;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8860 =
                     let uu____8861 =
                       let uu____8876 =
                         let uu____8877 =
                           let uu____8880 =
                             let uu____8881 =
                               let uu____8888 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____8888)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____8881  in
                           FStar_Pervasives_Native.Some uu____8880  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____8877
                          in
                       (uu____8876, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____8861  in
                   FStar_All.pipe_left mk1 uu____8860  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8919 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8923 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
                 in
              match uu____8923 with
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
                  let uu____8942 =
                    let uu____8943 =
                      let uu____8958 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual
                         in
                      let uu____8959 =
                        let uu____8962 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____8962]  in
                      (uu____8958, uu____8959)  in
                    FStar_Syntax_Syntax.Tm_app uu____8943  in
                  FStar_All.pipe_left mk1 uu____8942))
        | FStar_Parser_AST.NamedTyp (uu____8967,e) when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8969 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8970 ->
            let uu____8971 =
              let uu____8976 =
                let uu____8977 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term" uu____8977  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____8976)  in
            FStar_Errors.raise_error uu____8971 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____8978,uu____8979,uu____8980) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____9009,uu____9010,uu____9011) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____9024,uu____9025,uu____9026) ->
            failwith "Not implemented yet"

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____9040 -> false
    | uu____9049 -> true

and (is_synth_by_tactic :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____9055 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid  in
          (match uu____9055 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____9059 -> false

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
           (fun uu____9096  ->
              match uu____9096 with
              | (a,imp) ->
                  let uu____9109 = desugar_term env a  in
                  arg_withimp_e imp uu____9109))

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
        let is_requires uu____9135 =
          match uu____9135 with
          | (t1,uu____9141) ->
              (match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Requires uu____9142 -> true
               | uu____9149 -> false)
           in
        let is_ensures uu____9157 =
          match uu____9157 with
          | (t1,uu____9163) ->
              (match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Ensures uu____9164 -> true
               | uu____9171 -> false)
           in
        let is_app head1 uu____9182 =
          match uu____9182 with
          | (t1,uu____9188) ->
              (match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____9190;
                      FStar_Parser_AST.level = uu____9191;_},uu____9192,uu____9193)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____9194 -> false)
           in
        let is_smt_pat uu____9202 =
          match uu____9202 with
          | (t1,uu____9208) ->
              (match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____9211);
                             FStar_Parser_AST.range = uu____9212;
                             FStar_Parser_AST.level = uu____9213;_},uu____9214)::uu____9215::[])
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
                             FStar_Parser_AST.range = uu____9254;
                             FStar_Parser_AST.level = uu____9255;_},uu____9256)::uu____9257::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____9282 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____9310 = head_and_args t1  in
          match uu____9310 with
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
                   let thunk_ens uu____9404 =
                     match uu____9404 with
                     | (e,i) ->
                         let uu____9415 = thunk_ens_ e  in (uu____9415, i)
                      in
                   let fail_lemma uu____9425 =
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
                         let uu____9505 =
                           let uu____9512 =
                             let uu____9519 = thunk_ens ens  in
                             [uu____9519; nil_pat]  in
                           req_true :: uu____9512  in
                         unit_tm :: uu____9505
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____9566 =
                           let uu____9573 =
                             let uu____9580 = thunk_ens ens  in
                             [uu____9580; nil_pat]  in
                           req :: uu____9573  in
                         unit_tm :: uu____9566
                     | ens::smtpat::[] when
                         (((Prims.op_Negation (is_requires ens)) &&
                             (let uu____9628 = is_smt_pat ens  in
                              Prims.op_Negation uu____9628))
                            && (Prims.op_Negation (is_decreases ens)))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____9629 =
                           let uu____9636 =
                             let uu____9643 = thunk_ens ens  in
                             [uu____9643; smtpat]  in
                           req_true :: uu____9636  in
                         unit_tm :: uu____9629
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____9690 =
                           let uu____9697 =
                             let uu____9704 = thunk_ens ens  in
                             [uu____9704; nil_pat; dec]  in
                           req_true :: uu____9697  in
                         unit_tm :: uu____9690
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9764 =
                           let uu____9771 =
                             let uu____9778 = thunk_ens ens  in
                             [uu____9778; smtpat; dec]  in
                           req_true :: uu____9771  in
                         unit_tm :: uu____9764
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____9838 =
                           let uu____9845 =
                             let uu____9852 = thunk_ens ens  in
                             [uu____9852; nil_pat; dec]  in
                           req :: uu____9845  in
                         unit_tm :: uu____9838
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9912 =
                           let uu____9919 =
                             let uu____9926 = thunk_ens ens  in
                             [uu____9926; smtpat]  in
                           req :: uu____9919  in
                         unit_tm :: uu____9912
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____9991 =
                           let uu____9998 =
                             let uu____10005 = thunk_ens ens  in
                             [uu____10005; dec; smtpat]  in
                           req :: uu____9998  in
                         unit_tm :: uu____9991
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____10067 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____10067, args)
               | FStar_Parser_AST.Name l when
                   (let uu____10095 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____10095
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____10113 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____10113
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
               | uu____10151 ->
                   let default_effect =
                     let uu____10153 = FStar_Options.ml_ish ()  in
                     if uu____10153
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____10156 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____10156
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
        let uu____10180 = pre_process_comp_typ t  in
        match uu____10180 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____10229 =
                       let uu____10234 =
                         let uu____10235 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____10235
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____10234)
                        in
                     fail () uu____10229)
                else Obj.repr ());
             (let is_universe uu____10244 =
                match uu____10244 with
                | (uu____10249,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____10251 = FStar_Util.take is_universe args  in
              match uu____10251 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____10310  ->
                         match uu____10310 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____10317 =
                    let uu____10332 = FStar_List.hd args1  in
                    let uu____10341 = FStar_List.tl args1  in
                    (uu____10332, uu____10341)  in
                  (match uu____10317 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____10396 =
                         let is_decrease uu____10432 =
                           match uu____10432 with
                           | (t1,uu____10442) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____10452;
                                       FStar_Syntax_Syntax.vars = uu____10453;_},uu____10454::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10485 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____10396 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10599  ->
                                      match uu____10599 with
                                      | (t1,uu____10609) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10618,(arg,uu____10620)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10649 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____10662 -> false  in
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
                                           | uu____10802 -> pat  in
                                         let uu____10803 =
                                           let uu____10814 =
                                             let uu____10825 =
                                               let uu____10834 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____10834, aq)  in
                                             [uu____10825]  in
                                           ens :: uu____10814  in
                                         req :: uu____10803
                                     | uu____10875 -> rest2
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
        | uu____10897 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___127_10914 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___127_10914.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___127_10914.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___128_10948 = b  in
             {
               FStar_Parser_AST.b = (uu___128_10948.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___128_10948.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___128_10948.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____11007 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____11007)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____11020 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____11020 with
             | (env1,a1) ->
                 let a2 =
                   let uu___129_11030 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___129_11030.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___129_11030.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____11052 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____11066 =
                     let uu____11069 =
                       let uu____11070 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____11070]  in
                     no_annot_abs uu____11069 body2  in
                   FStar_All.pipe_left setpos uu____11066  in
                 let uu____11075 =
                   let uu____11076 =
                     let uu____11091 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____11092 =
                       let uu____11095 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____11095]  in
                     (uu____11091, uu____11092)  in
                   FStar_Syntax_Syntax.Tm_app uu____11076  in
                 FStar_All.pipe_left mk1 uu____11075)
        | uu____11100 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____11172 = q (rest, pats, body)  in
              let uu____11179 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____11172 uu____11179
                FStar_Parser_AST.Formula
               in
            let uu____11180 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____11180 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____11189 -> failwith "impossible"  in
      match f.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____11198,uu____11199) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____11210,uu____11211) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11242 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____11242
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11278 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____11278
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | uu____11320 -> desugar_term env f

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
      let uu____11325 =
        FStar_List.fold_left
          (fun uu____11361  ->
             fun b  ->
               match uu____11361 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___130_11413 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___130_11413.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___130_11413.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___130_11413.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11430 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____11430 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___131_11450 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_11450.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_11450.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11467 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____11325 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____11554 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11554)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11559 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11559)
      | FStar_Parser_AST.TVariable x ->
          let uu____11563 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____11563)
      | FStar_Parser_AST.NoName t ->
          let uu____11571 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____11571)
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
               (fun uu___94_11604  ->
                  match uu___94_11604 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11605 -> false))
           in
        let quals2 q =
          let uu____11616 =
            (let uu____11619 = FStar_ToSyntax_Env.iface env  in
             Prims.op_Negation uu____11619) ||
              (FStar_ToSyntax_Env.admitted_iface env)
             in
          if uu____11616
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____11632 =
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
                  FStar_Syntax_Syntax.sigquals = uu____11632;
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
            let uu____11663 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11693  ->
                        match uu____11693 with
                        | (x,uu____11701) ->
                            let uu____11702 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____11702 with
                             | (field_name,uu____11710) ->
                                 let only_decl =
                                   ((let uu____11714 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11714)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11716 =
                                        let uu____11717 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____11717.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____11716)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11731 =
                                       FStar_List.filter
                                         (fun uu___95_11735  ->
                                            match uu___95_11735 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11736 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11731
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___96_11749  ->
                                             match uu___96_11749 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11750 -> false))
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
                                      let uu____11758 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____11758
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____11763 =
                                        let uu____11768 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____11768  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11763;
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
                                      let uu____11772 =
                                        let uu____11773 =
                                          let uu____11780 =
                                            let uu____11783 =
                                              let uu____11784 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____11784
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____11783]  in
                                          ((false, [lb]), uu____11780)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11773
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11772;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____11663 FStar_List.flatten
  
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
            (lid,uu____11828,t,uu____11830,n1,uu____11832) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11837 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____11837 with
             | (formals,uu____11853) ->
                 (match formals with
                  | [] -> []
                  | uu____11876 ->
                      let filter_records uu___97_11888 =
                        match uu___97_11888 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11891,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11903 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____11905 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____11905 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____11915 = FStar_Util.first_N n1 formals  in
                      (match uu____11915 with
                       | (uu____11938,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11964 -> []
  
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
                    let uu____12014 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____12014
                    then
                      let uu____12017 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____12017
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____12020 =
                      let uu____12025 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____12025  in
                    let uu____12026 =
                      let uu____12029 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____12029  in
                    let uu____12032 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____12020;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____12026;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____12032;
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
          let tycon_id uu___98_12079 =
            match uu___98_12079 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____12081,uu____12082) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____12092,uu____12093,uu____12094) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____12104,uu____12105,uu____12106) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____12136,uu____12137,uu____12138) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____12180) ->
                let uu____12181 =
                  let uu____12182 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12182  in
                FStar_Parser_AST.mk_term uu____12181 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____12184 =
                  let uu____12185 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12185  in
                FStar_Parser_AST.mk_term uu____12184 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____12187) ->
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
              | uu____12210 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____12216 =
                     let uu____12217 =
                       let uu____12224 = binder_to_term b  in
                       (out, uu____12224, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____12217  in
                   FStar_Parser_AST.mk_term uu____12216
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___99_12234 =
            match uu___99_12234 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____12289  ->
                       match uu____12289 with
                       | (x,t,uu____12300) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____12306 =
                    let uu____12307 =
                      let uu____12308 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____12308  in
                    FStar_Parser_AST.mk_term uu____12307
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____12306 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____12312 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____12339  ->
                          match uu____12339 with
                          | (x,uu____12349,uu____12350) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____12312)
            | uu____12403 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___100_12434 =
            match uu___100_12434 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____12458 = typars_of_binders _env binders  in
                (match uu____12458 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____12504 =
                         let uu____12505 =
                           let uu____12506 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____12506  in
                         FStar_Parser_AST.mk_term uu____12505
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____12504 binders  in
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
            | uu____12519 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____12563 =
              FStar_List.fold_left
                (fun uu____12603  ->
                   fun uu____12604  ->
                     match (uu____12603, uu____12604) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12695 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____12695 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____12563 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12808 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____12808
                | uu____12809 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____12817 = desugar_abstract_tc quals env [] tc  in
              (match uu____12817 with
               | (uu____12830,uu____12831,se,uu____12833) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12836,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12853 =
                                 let uu____12854 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____12854  in
                               if uu____12853
                               then
                                 let uu____12855 =
                                   let uu____12860 =
                                     let uu____12861 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____12861
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____12860)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12855
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
                           | uu____12868 ->
                               let uu____12869 =
                                 let uu____12872 =
                                   let uu____12873 =
                                     let uu____12886 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____12886)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12873
                                    in
                                 FStar_Syntax_Syntax.mk uu____12872  in
                               uu____12869 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___132_12890 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___132_12890.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___132_12890.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___132_12890.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12893 -> failwith "Impossible"  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   let env2 =
                     let uu____12896 = FStar_ToSyntax_Env.qualify env1 id1
                        in
                     FStar_ToSyntax_Env.push_doc env1 uu____12896
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____12911 = typars_of_binders env binders  in
              (match uu____12911 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12947 =
                           FStar_Util.for_some
                             (fun uu___101_12949  ->
                                match uu___101_12949 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12950 -> false) quals
                            in
                         if uu____12947
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____12957 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___102_12961  ->
                               match uu___102_12961 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12962 -> false))
                        in
                     if uu____12957
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_ToSyntax_Env.qualify env id1  in
                   let se =
                     let uu____12971 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____12971
                     then
                       let uu____12974 =
                         match t.FStar_Parser_AST.tm with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____13001 =
                               match FStar_List.rev args with
                               | (last_arg,uu____13031)::args_rev ->
                                   (match last_arg.FStar_Parser_AST.tm with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____13070 -> ([], args))
                               | uu____13079 -> ([], args)  in
                             (match uu____13001 with
                              | (cattributes,args1) ->
                                  let uu____13118 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____13118))
                         | uu____13129 -> (t, [])  in
                       match uu____12974 with
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
                                  (fun uu___103_13151  ->
                                     match uu___103_13151 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____13152 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____13163)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____13187 = tycon_record_as_variant trec  in
              (match uu____13187 with
               | (t,fs) ->
                   let uu____13204 =
                     let uu____13207 =
                       let uu____13208 =
                         let uu____13217 =
                           let uu____13220 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____13220  in
                         (uu____13217, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____13208  in
                     uu____13207 :: quals  in
                   desugar_tycon env d uu____13204 [t])
          | uu____13225::uu____13226 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____13387 = et  in
                match uu____13387 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13612 ->
                         let trec = tc  in
                         let uu____13636 = tycon_record_as_variant trec  in
                         (match uu____13636 with
                          | (t,fs) ->
                              let uu____13695 =
                                let uu____13698 =
                                  let uu____13699 =
                                    let uu____13708 =
                                      let uu____13711 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____13711  in
                                    (uu____13708, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____13699
                                   in
                                uu____13698 :: quals1  in
                              collect_tcs uu____13695 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____13798 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____13798 with
                          | (env2,uu____13858,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____14007 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____14007 with
                          | (env2,uu____14067,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____14192 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____14239 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____14239 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___105_14750  ->
                             match uu___105_14750 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____14817,uu____14818);
                                    FStar_Syntax_Syntax.sigrng = uu____14819;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14820;
                                    FStar_Syntax_Syntax.sigmeta = uu____14821;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14822;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14883 =
                                     typars_of_binders env1 binders  in
                                   match uu____14883 with
                                   | (env2,tpars1) ->
                                       let uu____14914 =
                                         push_tparams env2 tpars1  in
                                       (match uu____14914 with
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
                                 let uu____14947 =
                                   let uu____14968 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____14968)
                                    in
                                 [uu____14947]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____15036);
                                    FStar_Syntax_Syntax.sigrng = uu____15037;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____15039;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____15040;_},constrs,tconstr,quals1)
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
                                 let uu____15136 = push_tparams env1 tpars
                                    in
                                 (match uu____15136 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____15213  ->
                                             match uu____15213 with
                                             | (x,uu____15227) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____15235 =
                                        let uu____15264 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____15378  ->
                                                  match uu____15378 with
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
                                                        let uu____15434 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____15434
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
                                                                uu___104_15445
                                                                 ->
                                                                match uu___104_15445
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15457
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____15465 =
                                                        let uu____15486 =
                                                          let uu____15487 =
                                                            let uu____15488 =
                                                              let uu____15503
                                                                =
                                                                let uu____15506
                                                                  =
                                                                  let uu____15509
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15509
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15506
                                                                 in
                                                              (name, univs1,
                                                                uu____15503,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15488
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15487;
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
                                                          uu____15486)
                                                         in
                                                      (name, uu____15465)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____15264
                                         in
                                      (match uu____15235 with
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
                             | uu____15748 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15880  ->
                             match uu____15880 with
                             | (name_doc,uu____15908,uu____15909) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15989  ->
                             match uu____15989 with
                             | (uu____16010,uu____16011,se) -> se))
                      in
                   let uu____16041 =
                     let uu____16048 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____16048 rng
                      in
                   (match uu____16041 with
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
                               (fun uu____16114  ->
                                  match uu____16114 with
                                  | (uu____16137,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____16188,tps,k,uu____16191,constrs)
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
                                  | uu____16210 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____16227  ->
                                 match uu____16227 with
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
      let uu____16262 =
        FStar_List.fold_left
          (fun uu____16285  ->
             fun b  ->
               match uu____16285 with
               | (env1,binders1) ->
                   let uu____16305 = desugar_binder env1 b  in
                   (match uu____16305 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16322 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____16322 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____16339 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____16262 with
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
          let uu____16384 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___106_16389  ->
                    match uu___106_16389 with
                    | FStar_Syntax_Syntax.Reflectable uu____16390 -> true
                    | uu____16391 -> false))
             in
          if uu____16384
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
                let uu____16490 = desugar_binders monad_env eff_binders  in
                match uu____16490 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____16511 =
                        let uu____16512 =
                          let uu____16519 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          FStar_Pervasives_Native.fst uu____16519  in
                        FStar_List.length uu____16512  in
                      uu____16511 = (Prims.parse_int "1")  in
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
                          (uu____16561,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16563,uu____16564,uu____16565),uu____16566)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16599 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____16600 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16612 = name_of_eff_decl decl  in
                           FStar_List.mem uu____16612 mandatory_members)
                        eff_decls
                       in
                    (match uu____16600 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16629 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16658  ->
                                   fun decl  ->
                                     match uu____16658 with
                                     | (env2,out) ->
                                         let uu____16678 =
                                           desugar_decl env2 decl  in
                                         (match uu____16678 with
                                          | (env3,ses) ->
                                              let uu____16691 =
                                                let uu____16694 =
                                                  FStar_List.hd ses  in
                                                uu____16694 :: out  in
                                              (env3, uu____16691)))
                                (env1, []))
                            in
                         (match uu____16629 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16762,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16765,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16766,
                                                                (def,uu____16768)::
                                                                (cps_type,uu____16770)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16771;
                                                             FStar_Parser_AST.level
                                                               = uu____16772;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16824 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16824 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16844 =
                                                   let uu____16845 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____16846 =
                                                     let uu____16847 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16847
                                                      in
                                                   let uu____16852 =
                                                     let uu____16853 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16853
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16845;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16846;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16852
                                                   }  in
                                                 (uu____16844, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16860,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16863,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16898 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16898 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16918 =
                                                   let uu____16919 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____16920 =
                                                     let uu____16921 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16921
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16919;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16920;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____16918, doc1))
                                        | uu____16928 ->
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
                                let uu____16958 =
                                  let uu____16959 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16959
                                   in
                                ([], uu____16958)  in
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
                                    let uu____16976 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____16976)  in
                                  let uu____16983 =
                                    let uu____16984 =
                                      let uu____16985 =
                                        let uu____16986 = lookup "repr"  in
                                        FStar_Pervasives_Native.snd
                                          uu____16986
                                         in
                                      let uu____16995 = lookup "return"  in
                                      let uu____16996 = lookup "bind"  in
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
                                          uu____16985;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16995;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16996;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16984
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16983;
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
                                       (fun uu___107_17000  ->
                                          match uu___107_17000 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____17001 -> true
                                          | uu____17002 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____17012 =
                                     let uu____17013 =
                                       let uu____17014 = lookup "return_wp"
                                          in
                                       let uu____17015 = lookup "bind_wp"  in
                                       let uu____17016 =
                                         lookup "if_then_else"  in
                                       let uu____17017 = lookup "ite_wp"  in
                                       let uu____17018 = lookup "stronger"
                                          in
                                       let uu____17019 = lookup "close_wp"
                                          in
                                       let uu____17020 = lookup "assert_p"
                                          in
                                       let uu____17021 = lookup "assume_p"
                                          in
                                       let uu____17022 = lookup "null_wp"  in
                                       let uu____17023 = lookup "trivial"  in
                                       let uu____17024 =
                                         if rr
                                         then
                                           let uu____17025 = lookup "repr"
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____17025
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____17041 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____17043 =
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
                                           uu____17014;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____17015;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____17016;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____17017;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____17018;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____17019;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____17020;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____17021;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____17022;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____17023;
                                         FStar_Syntax_Syntax.repr =
                                           uu____17024;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____17041;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____17043;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____17013
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____17012;
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
                                        fun uu____17068  ->
                                          match uu____17068 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____17082 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____17082
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
                let uu____17106 = desugar_binders env1 eff_binders  in
                match uu____17106 with
                | (env2,binders) ->
                    let uu____17125 =
                      let uu____17144 = head_and_args defn  in
                      match uu____17144 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____17189 ->
                                let uu____17190 =
                                  let uu____17195 =
                                    let uu____17196 =
                                      let uu____17197 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____17197 " not found"
                                       in
                                    Prims.strcat "Effect " uu____17196  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____17195)
                                   in
                                FStar_Errors.raise_error uu____17190
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____17199 =
                            match FStar_List.rev args with
                            | (last_arg,uu____17229)::args_rev ->
                                (match last_arg.FStar_Parser_AST.tm with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____17268 -> ([], args))
                            | uu____17277 -> ([], args)  in
                          (match uu____17199 with
                           | (cattributes,args1) ->
                               let uu____17328 = desugar_args env2 args1  in
                               let uu____17337 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____17328, uu____17337))
                       in
                    (match uu____17125 with
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
                          (let uu____17393 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____17393 with
                           | (ed_binders,uu____17407,ed_binders_opening) ->
                               let sub1 uu____17418 =
                                 match uu____17418 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____17432 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____17432 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____17436 =
                                       let uu____17437 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____17437)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____17436
                                  in
                               let mname =
                                 FStar_ToSyntax_Env.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____17442 =
                                   let uu____17443 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____17443
                                    in
                                 let uu____17454 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____17455 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____17456 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____17457 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____17458 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____17459 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____17460 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____17461 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____17462 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____17463 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____17464 =
                                   let uu____17465 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____17465
                                    in
                                 let uu____17476 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____17477 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____17478 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____17486 =
                                          FStar_ToSyntax_Env.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____17487 =
                                          let uu____17488 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17488
                                           in
                                        let uu____17499 =
                                          let uu____17500 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17500
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____17486;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____17487;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____17499
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
                                     uu____17442;
                                   FStar_Syntax_Syntax.ret_wp = uu____17454;
                                   FStar_Syntax_Syntax.bind_wp = uu____17455;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____17456;
                                   FStar_Syntax_Syntax.ite_wp = uu____17457;
                                   FStar_Syntax_Syntax.stronger = uu____17458;
                                   FStar_Syntax_Syntax.close_wp = uu____17459;
                                   FStar_Syntax_Syntax.assert_p = uu____17460;
                                   FStar_Syntax_Syntax.assume_p = uu____17461;
                                   FStar_Syntax_Syntax.null_wp = uu____17462;
                                   FStar_Syntax_Syntax.trivial = uu____17463;
                                   FStar_Syntax_Syntax.repr = uu____17464;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____17476;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____17477;
                                   FStar_Syntax_Syntax.actions = uu____17478
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____17513 =
                                     let uu____17514 =
                                       let uu____17521 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____17521
                                        in
                                     FStar_List.length uu____17514  in
                                   uu____17513 = (Prims.parse_int "1")  in
                                 let uu____17550 =
                                   let uu____17553 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____17553 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____17550;
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
                                             let uu____17573 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                in
                                             FStar_ToSyntax_Env.push_sigelt
                                               env5 uu____17573
                                              in
                                           FStar_ToSyntax_Env.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____17575 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____17575
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
    let uu____17590 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____17590 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____17641 ->
              let uu____17642 =
                let uu____17643 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____17643
                 in
              Prims.strcat "\n  " uu____17642
          | uu____17644 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____17657  ->
               match uu____17657 with
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
          let uu____17675 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____17675
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____17677 =
          let uu____17686 = FStar_Syntax_Syntax.as_arg arg  in [uu____17686]
           in
        FStar_Syntax_Util.mk_app fv uu____17677

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____17693 = desugar_decl_noattrs env d  in
      match uu____17693 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____17713 = mk_comment_attr d  in uu____17713 :: attrs1  in
          let s =
            FStar_List.fold_left
              (fun s  ->
                 fun a  ->
                   let uu____17724 =
                     let uu____17725 = FStar_Syntax_Print.term_to_string a
                        in
                     Prims.strcat "; " uu____17725  in
                   Prims.strcat s uu____17724) "" attrs2
             in
          let uu____17726 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___133_17732 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___133_17732.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___133_17732.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_17732.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_17732.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____17726)

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
      | FStar_Parser_AST.Fsdoc uu____17758 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17774 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____17774, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____17813  ->
                 match uu____17813 with | (x,uu____17821) -> x) tcs
             in
          let uu____17826 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____17826 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17848;
                    FStar_Parser_AST.prange = uu____17849;_},uu____17850)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17859;
                    FStar_Parser_AST.prange = uu____17860;_},uu____17861)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17876;
                         FStar_Parser_AST.prange = uu____17877;_},uu____17878);
                    FStar_Parser_AST.prange = uu____17879;_},uu____17880)::[]
                   -> false
               | (p,uu____17896)::[] ->
                   let uu____17905 = is_app_pattern p  in
                   Prims.op_Negation uu____17905
               | uu____17906 -> false)
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
            let uu____17980 =
              let uu____17981 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____17981.FStar_Syntax_Syntax.n  in
            (match uu____17980 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17989) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____18022::uu____18023 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____18026 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___108_18040  ->
                               match uu___108_18040 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____18043;
                                   FStar_Syntax_Syntax.lbunivs = uu____18044;
                                   FStar_Syntax_Syntax.lbtyp = uu____18045;
                                   FStar_Syntax_Syntax.lbeff = uu____18046;
                                   FStar_Syntax_Syntax.lbdef = uu____18047;
                                   FStar_Syntax_Syntax.lbattrs = uu____18048;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____18060;
                                   FStar_Syntax_Syntax.lbtyp = uu____18061;
                                   FStar_Syntax_Syntax.lbeff = uu____18062;
                                   FStar_Syntax_Syntax.lbdef = uu____18063;
                                   FStar_Syntax_Syntax.lbattrs = uu____18064;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____18078 =
                     FStar_All.pipe_right lets1
                       (FStar_Util.for_some
                          (fun uu____18109  ->
                             match uu____18109 with
                             | (uu____18122,(uu____18123,t)) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____18078
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____18147 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____18147
                   then
                     let uu____18156 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___134_18170 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___135_18172 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___135_18172.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___135_18172.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___134_18170.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___134_18170.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___134_18170.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___134_18170.FStar_Syntax_Syntax.lbdef);
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___134_18170.FStar_Syntax_Syntax.lbattrs)
                               }))
                        in
                     ((FStar_Pervasives_Native.fst lbs), uu____18156)
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
             | uu____18207 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____18213 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____18232 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____18213 with
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
                       let uu___136_18256 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___136_18256.FStar_Parser_AST.prange)
                       }
                   | uu____18257 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___137_18264 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___137_18264.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___137_18264.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___137_18264.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____18296 id1 =
                   match uu____18296 with
                   | (env1,ses) ->
                       let main =
                         let uu____18317 =
                           let uu____18318 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____18318  in
                         FStar_Parser_AST.mk_term uu____18317
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
                       let uu____18368 = desugar_decl env1 id_decl  in
                       (match uu____18368 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____18386 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____18386 FStar_Util.set_elements
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
            let uu____18417 = close_fun env t  in
            desugar_term env uu____18417  in
          let quals1 =
            let uu____18421 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env)
               in
            if uu____18421
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_ToSyntax_Env.qualify env id1  in
          let se =
            let uu____18427 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____18427;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____18439 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____18439 with
           | (t,uu____18453) ->
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
            let uu____18487 =
              let uu____18494 = FStar_Syntax_Syntax.null_binder t  in
              [uu____18494]  in
            let uu____18495 =
              let uu____18498 =
                let uu____18499 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____18499  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____18498
               in
            FStar_Syntax_Util.arrow uu____18487 uu____18495  in
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
            let uu____18561 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____18561 with
            | FStar_Pervasives_Native.None  ->
                let uu____18564 =
                  let uu____18569 =
                    let uu____18570 =
                      let uu____18571 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____18571 " not found"  in
                    Prims.strcat "Effect name " uu____18570  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____18569)  in
                FStar_Errors.raise_error uu____18564
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____18575 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18617 =
                  let uu____18626 =
                    let uu____18633 = desugar_term env t  in
                    ([], uu____18633)  in
                  FStar_Pervasives_Native.Some uu____18626  in
                (uu____18617, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18666 =
                  let uu____18675 =
                    let uu____18682 = desugar_term env wp  in
                    ([], uu____18682)  in
                  FStar_Pervasives_Native.Some uu____18675  in
                let uu____18691 =
                  let uu____18700 =
                    let uu____18707 = desugar_term env t  in
                    ([], uu____18707)  in
                  FStar_Pervasives_Native.Some uu____18700  in
                (uu____18666, uu____18691)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18733 =
                  let uu____18742 =
                    let uu____18749 = desugar_term env t  in
                    ([], uu____18749)  in
                  FStar_Pervasives_Native.Some uu____18742  in
                (FStar_Pervasives_Native.None, uu____18733)
             in
          (match uu____18575 with
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
      let uu____18837 =
        FStar_List.fold_left
          (fun uu____18857  ->
             fun d  ->
               match uu____18857 with
               | (env1,sigelts) ->
                   let uu____18877 = desugar_decl env1 d  in
                   (match uu____18877 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____18837 with
      | (env1,sigelts) ->
          let rec forward acc uu___110_18918 =
            match uu___110_18918 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18932,FStar_Syntax_Syntax.Sig_let uu____18933) ->
                     let uu____18946 =
                       let uu____18949 =
                         let uu___138_18950 = se2  in
                         let uu____18951 =
                           let uu____18954 =
                             FStar_List.filter
                               (fun uu___109_18968  ->
                                  match uu___109_18968 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____18972;
                                           FStar_Syntax_Syntax.vars =
                                             uu____18973;_},uu____18974);
                                      FStar_Syntax_Syntax.pos = uu____18975;
                                      FStar_Syntax_Syntax.vars = uu____18976;_}
                                      when
                                      let uu____18999 =
                                        let uu____19000 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____19000
                                         in
                                      uu____18999 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____19001 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____18954
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___138_18950.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___138_18950.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___138_18950.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___138_18950.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____18951
                         }  in
                       uu____18949 :: se1 :: acc  in
                     forward uu____18946 sigelts1
                 | uu____19006 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____19014 = forward [] sigelts  in (env1, uu____19014)
  
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
          | (FStar_Pervasives_Native.None ,uu____19065) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____19069;
               FStar_Syntax_Syntax.exports = uu____19070;
               FStar_Syntax_Syntax.is_interface = uu____19071;_},FStar_Parser_AST.Module
             (current_lid,uu____19073)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____19081) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____19084 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____19120 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname FStar_ToSyntax_Env.default_mii
                 in
              (uu____19120, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____19137 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname FStar_ToSyntax_Env.default_mii
                 in
              (uu____19137, mname, decls, false)
           in
        match uu____19084 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____19167 = desugar_decls env2 decls  in
            (match uu____19167 with
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
          let uu____19221 =
            (FStar_Options.interactive ()) &&
              (let uu____19223 =
                 let uu____19224 =
                   let uu____19225 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____19225  in
                 FStar_Util.get_file_extension uu____19224  in
               FStar_List.mem uu____19223 ["fsti"; "fsi"])
             in
          if uu____19221 then as_interface m else m  in
        let uu____19229 = desugar_modul_common curmod env m1  in
        match uu____19229 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____19244 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____19260 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____19260 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____19276 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____19276
            then
              let uu____19277 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____19277
            else ());
           (let uu____19279 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____19279, modul)))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____19293 = desugar_modul env modul  in
      match uu____19293 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____19320 = desugar_decls env decls  in
      match uu____19320 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____19358 = desugar_partial_modul modul env a_modul  in
        match uu____19358 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____19432 ->
                  let t =
                    let uu____19440 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____19440  in
                  let uu____19449 =
                    let uu____19450 = FStar_Syntax_Subst.compress t  in
                    uu____19450.FStar_Syntax_Syntax.n  in
                  (match uu____19449 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____19460,uu____19461)
                       -> bs1
                   | uu____19482 -> failwith "Impossible")
               in
            let uu____19489 =
              let uu____19496 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____19496
                FStar_Syntax_Syntax.t_unit
               in
            match uu____19489 with
            | (binders,uu____19498,binders_opening) ->
                let erase_term t =
                  let uu____19504 =
                    let uu____19505 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____19505  in
                  FStar_Syntax_Subst.close binders uu____19504  in
                let erase_tscheme uu____19521 =
                  match uu____19521 with
                  | (us,t) ->
                      let t1 =
                        let uu____19541 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____19541 t  in
                      let uu____19544 =
                        let uu____19545 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____19545  in
                      ([], uu____19544)
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
                    | uu____19574 ->
                        let bs =
                          let uu____19582 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____19582  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____19612 =
                          let uu____19613 =
                            let uu____19616 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____19616  in
                          uu____19613.FStar_Syntax_Syntax.n  in
                        (match uu____19612 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____19624,uu____19625) -> bs1
                         | uu____19646 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____19657 =
                      let uu____19658 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____19658  in
                    FStar_Syntax_Subst.close binders uu____19657  in
                  let uu___139_19659 = action  in
                  let uu____19660 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____19661 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___139_19659.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___139_19659.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____19660;
                    FStar_Syntax_Syntax.action_typ = uu____19661
                  }  in
                let uu___140_19662 = ed  in
                let uu____19663 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____19664 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____19665 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____19666 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____19667 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____19668 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____19669 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____19670 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____19671 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____19672 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____19673 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____19674 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____19675 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____19676 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____19677 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____19678 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___140_19662.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___140_19662.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____19663;
                  FStar_Syntax_Syntax.signature = uu____19664;
                  FStar_Syntax_Syntax.ret_wp = uu____19665;
                  FStar_Syntax_Syntax.bind_wp = uu____19666;
                  FStar_Syntax_Syntax.if_then_else = uu____19667;
                  FStar_Syntax_Syntax.ite_wp = uu____19668;
                  FStar_Syntax_Syntax.stronger = uu____19669;
                  FStar_Syntax_Syntax.close_wp = uu____19670;
                  FStar_Syntax_Syntax.assert_p = uu____19671;
                  FStar_Syntax_Syntax.assume_p = uu____19672;
                  FStar_Syntax_Syntax.null_wp = uu____19673;
                  FStar_Syntax_Syntax.trivial = uu____19674;
                  FStar_Syntax_Syntax.repr = uu____19675;
                  FStar_Syntax_Syntax.return_repr = uu____19676;
                  FStar_Syntax_Syntax.bind_repr = uu____19677;
                  FStar_Syntax_Syntax.actions = uu____19678
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___141_19690 = se  in
                  let uu____19691 =
                    let uu____19692 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____19692  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19691;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___141_19690.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___141_19690.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___141_19690.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___141_19690.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___142_19696 = se  in
                  let uu____19697 =
                    let uu____19698 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19698
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19697;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___142_19696.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___142_19696.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___142_19696.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___142_19696.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____19700 -> FStar_ToSyntax_Env.push_sigelt env se  in
          let uu____19701 =
            FStar_ToSyntax_Env.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____19701 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____19713 =
                  FStar_ToSyntax_Env.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____19713
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_ToSyntax_Env.finish en2 m  in
              let uu____19715 =
                if pop_when_done
                then
                  FStar_ToSyntax_Env.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____19715)
  