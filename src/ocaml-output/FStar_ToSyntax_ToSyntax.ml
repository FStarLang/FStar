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
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____178 =
        let uu____179 = unparen t  in uu____179.FStar_Parser_AST.tm  in
      match uu____178 with
      | FStar_Parser_AST.Name l ->
          let uu____181 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____181 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____187) ->
          let uu____200 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
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
    FStar_ToSyntax_Env.env ->
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
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____274 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____273  in
          let fallback uu____280 =
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
                let uu____283 = FStar_Options.ml_ish ()  in
                if uu____283
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
            | uu____287 -> FStar_Pervasives_Native.None  in
          let uu____288 =
            let uu____295 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_ToSyntax_Env.try_lookup_lid env uu____295  in
          match uu____288 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____307 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____323 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____323
  
let rec (free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____362 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____366 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____366 with | (env1,uu____378) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____381,term) ->
          let uu____383 = free_type_vars env term  in (env, uu____383)
      | FStar_Parser_AST.TAnnotated (id1,uu____389) ->
          let uu____390 = FStar_ToSyntax_Env.push_bv env id1  in
          (match uu____390 with | (env1,uu____402) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____406 = free_type_vars env t  in (env, uu____406)

and (free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____413 =
        let uu____414 = unparen t  in uu____414.FStar_Parser_AST.tm  in
      match uu____413 with
      | FStar_Parser_AST.Labeled uu____417 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____427 = FStar_ToSyntax_Env.try_lookup_id env a  in
          (match uu____427 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____440 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____447 -> []
      | FStar_Parser_AST.Uvar uu____448 -> []
      | FStar_Parser_AST.Var uu____449 -> []
      | FStar_Parser_AST.Projector uu____450 -> []
      | FStar_Parser_AST.Discrim uu____455 -> []
      | FStar_Parser_AST.Name uu____456 -> []
      | FStar_Parser_AST.Requires (t1,uu____458) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____464) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____469,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____487,ts) ->
          FStar_List.collect
            (fun uu____508  ->
               match uu____508 with | (t1,uu____516) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____517,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____525) ->
          let uu____526 = free_type_vars env t1  in
          let uu____529 = free_type_vars env t2  in
          FStar_List.append uu____526 uu____529
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____534 = free_type_vars_b env b  in
          (match uu____534 with
           | (env1,f) ->
               let uu____549 = free_type_vars env1 t1  in
               FStar_List.append f uu____549)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____558 =
            FStar_List.fold_left
              (fun uu____578  ->
                 fun binder  ->
                   match uu____578 with
                   | (env1,free) ->
                       let uu____598 = free_type_vars_b env1 binder  in
                       (match uu____598 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____558 with
           | (env1,free) ->
               let uu____629 = free_type_vars env1 body  in
               FStar_List.append free uu____629)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____638 =
            FStar_List.fold_left
              (fun uu____658  ->
                 fun binder  ->
                   match uu____658 with
                   | (env1,free) ->
                       let uu____678 = free_type_vars_b env1 binder  in
                       (match uu____678 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____638 with
           | (env1,free) ->
               let uu____709 = free_type_vars env1 body  in
               FStar_List.append free uu____709)
      | FStar_Parser_AST.Project (t1,uu____713) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____717 -> []
      | FStar_Parser_AST.Let uu____724 -> []
      | FStar_Parser_AST.LetOpen uu____745 -> []
      | FStar_Parser_AST.If uu____750 -> []
      | FStar_Parser_AST.QForall uu____757 -> []
      | FStar_Parser_AST.QExists uu____770 -> []
      | FStar_Parser_AST.Record uu____783 -> []
      | FStar_Parser_AST.Match uu____796 -> []
      | FStar_Parser_AST.TryWith uu____811 -> []
      | FStar_Parser_AST.Bind uu____826 -> []
      | FStar_Parser_AST.Seq uu____833 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____880 =
        let uu____881 = unparen t1  in uu____881.FStar_Parser_AST.tm  in
      match uu____880 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____923 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____943 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____943  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____961 =
                     let uu____962 =
                       let uu____967 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____967)  in
                     FStar_Parser_AST.TAnnotated uu____962  in
                   FStar_Parser_AST.mk_binder uu____961 x.FStar_Ident.idRange
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
        let uu____980 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____980  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____998 =
                     let uu____999 =
                       let uu____1004 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1004)  in
                     FStar_Parser_AST.TAnnotated uu____999  in
                   FStar_Parser_AST.mk_binder uu____998 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1006 =
             let uu____1007 = unparen t  in uu____1007.FStar_Parser_AST.tm
              in
           match uu____1006 with
           | FStar_Parser_AST.Product uu____1008 -> t
           | uu____1015 ->
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
      | uu____1047 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1053,uu____1054) -> true
    | FStar_Parser_AST.PatVar (uu____1059,uu____1060) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1066) -> is_var_pattern p1
    | uu____1067 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1072) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1073;
           FStar_Parser_AST.prange = uu____1074;_},uu____1075)
        -> true
    | uu____1086 -> false
  
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
    | uu____1090 -> p
  
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
            let uu____1130 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1130 with
             | (name,args,uu____1161) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1187);
               FStar_Parser_AST.prange = uu____1188;_},args)
            when is_top_level1 ->
            let uu____1198 =
              let uu____1203 = FStar_ToSyntax_Env.qualify env id1  in
              FStar_Util.Inr uu____1203  in
            (uu____1198, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1213);
               FStar_Parser_AST.prange = uu____1214;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1232 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1270 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1271,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1274 -> acc
      | FStar_Parser_AST.PatTvar uu____1275 -> acc
      | FStar_Parser_AST.PatOp uu____1282 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1290) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1299) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1314 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1314
      | FStar_Parser_AST.PatAscribed (pat,uu____1322) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1360 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1388 -> false
  
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
  fun uu___86_1414  ->
    match uu___86_1414 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1421 -> failwith "Impossible"
  
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
      fun uu___87_1446  ->
        match uu___87_1446 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1462 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1462, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1467 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____1467 with
             | (env1,a1) ->
                 (((let uu___111_1487 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___111_1487.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___111_1487.FStar_Syntax_Syntax.index);
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
  fun uu____1512  ->
    match uu____1512 with
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
      let uu____1577 =
        let uu____1592 =
          let uu____1593 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1593  in
        let uu____1594 =
          let uu____1603 =
            let uu____1610 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1610)  in
          [uu____1603]  in
        (uu____1592, uu____1594)  in
      FStar_Syntax_Syntax.Tm_app uu____1577  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1643 =
        let uu____1658 =
          let uu____1659 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1659  in
        let uu____1660 =
          let uu____1669 =
            let uu____1676 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1676)  in
          [uu____1669]  in
        (uu____1658, uu____1660)  in
      FStar_Syntax_Syntax.Tm_app uu____1643  in
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
          let uu____1719 =
            let uu____1734 =
              let uu____1735 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____1735  in
            let uu____1736 =
              let uu____1745 =
                let uu____1752 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____1752)  in
              let uu____1755 =
                let uu____1764 =
                  let uu____1771 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____1771)  in
                [uu____1764]  in
              uu____1745 :: uu____1755  in
            (uu____1734, uu____1736)  in
          FStar_Syntax_Syntax.Tm_app uu____1719  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___88_1802  ->
    match uu___88_1802 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1803 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1811 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1811)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____1826 =
      let uu____1827 = unparen t  in uu____1827.FStar_Parser_AST.tm  in
    match uu____1826 with
    | FStar_Parser_AST.Wild  ->
        let uu____1832 =
          let uu____1833 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____1833  in
        FStar_Util.Inr uu____1832
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1844)) ->
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
             let uu____1910 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1910
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1921 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1921
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1932 =
               let uu____1937 =
                 let uu____1938 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____1938
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____1937)
                in
             FStar_Errors.raise_error uu____1932 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____1943 ->
        let rec aux t1 univargs =
          let uu____1973 =
            let uu____1974 = unparen t1  in uu____1974.FStar_Parser_AST.tm
             in
          match uu____1973 with
          | FStar_Parser_AST.App (t2,targ,uu____1981) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___89_2005  ->
                     match uu___89_2005 with
                     | FStar_Util.Inr uu____2010 -> true
                     | uu____2011 -> false) univargs
              then
                let uu____2016 =
                  let uu____2017 =
                    FStar_List.map
                      (fun uu___90_2026  ->
                         match uu___90_2026 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2017  in
                FStar_Util.Inr uu____2016
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___91_2043  ->
                        match uu___91_2043 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2049 -> failwith "impossible")
                     univargs
                    in
                 let uu____2050 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2050)
          | uu____2056 ->
              let uu____2057 =
                let uu____2062 =
                  let uu____2063 =
                    let uu____2064 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2064 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2063  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2062)  in
              FStar_Errors.raise_error uu____2057 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2073 ->
        let uu____2074 =
          let uu____2079 =
            let uu____2080 =
              let uu____2081 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2081 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2080  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2079)  in
        FStar_Errors.raise_error uu____2074 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields :
  'Auu____2100 .
    FStar_ToSyntax_Env.env ->
      (FStar_Ident.lident,'Auu____2100) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_ToSyntax_Env.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2125 = FStar_List.hd fields  in
        match uu____2125 with
        | (f,uu____2135) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2145 =
                match uu____2145 with
                | (f',uu____2151) ->
                    (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
                     (let uu____2153 =
                        FStar_ToSyntax_Env.belongs_to_record env f' record
                         in
                      if uu____2153
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
              (let uu____2157 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2157);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2374 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2381 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2382 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2384,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2425  ->
                          match uu____2425 with
                          | (p3,uu____2435) ->
                              let uu____2436 =
                                let uu____2437 =
                                  let uu____2440 = pat_vars p3  in
                                  FStar_Util.set_intersect uu____2440 out  in
                                FStar_Util.set_is_empty uu____2437  in
                              if uu____2436
                              then
                                let uu____2445 = pat_vars p3  in
                                FStar_Util.set_union out uu____2445
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                                    "Non-linear patterns are not permitted.")
                                  r) FStar_Syntax_Syntax.no_names)
             in
          pat_vars p1  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2452) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2453) -> ()
         | (true ,uu____2460) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____2495 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2495 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2509 ->
               let uu____2512 = push_bv_maybe_mut e x  in
               (match uu____2512 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2599 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2615 =
                 let uu____2616 =
                   let uu____2617 =
                     let uu____2624 =
                       let uu____2625 =
                         let uu____2630 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2630, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2625  in
                     (uu____2624, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2617  in
                 {
                   FStar_Parser_AST.pat = uu____2616;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2615
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2635 = aux loc env1 p2  in
               (match uu____2635 with
                | (loc1,env',binder,p3,imp) ->
                    let annot_pat_var p4 t1 =
                      match p4.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let uu___112_2689 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var
                                 (let uu___113_2694 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___113_2694.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___113_2694.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___112_2689.FStar_Syntax_Syntax.p)
                          }
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let uu___114_2696 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild
                                 (let uu___115_2701 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___115_2701.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___115_2701.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___114_2696.FStar_Syntax_Syntax.p)
                          }
                      | uu____2702 when top -> p4
                      | uu____2703 ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                              "Type ascriptions within patterns are only allowed on variables")
                            orig.FStar_Parser_AST.prange
                       in
                    let uu____2706 =
                      match binder with
                      | LetBinder uu____2719 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2733 = close_fun env1 t  in
                            desugar_term env1 uu____2733  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2735 -> true)
                           then
                             (let uu____2736 =
                                let uu____2741 =
                                  let uu____2742 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____2743 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____2744 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3
                                    "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                    uu____2742 uu____2743 uu____2744
                                   in
                                (FStar_Errors.Warning_MultipleAscriptions,
                                  uu____2741)
                                 in
                              FStar_Errors.log_issue
                                orig.FStar_Parser_AST.prange uu____2736)
                           else ();
                           (let uu____2746 = annot_pat_var p3 t1  in
                            (uu____2746,
                              (LocalBinder
                                 ((let uu___116_2752 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___116_2752.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___116_2752.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }), aq)))))
                       in
                    (match uu____2706 with
                     | (p4,binder1) -> (loc1, env', binder1, p4, imp)))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2774 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2774, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2785 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2785, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2806 = resolvex loc env1 x  in
               (match uu____2806 with
                | (loc1,env2,xbv) ->
                    let uu____2828 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2828, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2849 = resolvex loc env1 x  in
               (match uu____2849 with
                | (loc1,env2,xbv) ->
                    let uu____2871 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2871, imp))
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
               let uu____2883 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2883, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2907;_},args)
               ->
               let uu____2913 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2954  ->
                        match uu____2954 with
                        | (loc1,env2,args1) ->
                            let uu____3002 = aux loc1 env2 arg  in
                            (match uu____3002 with
                             | (loc2,env3,uu____3031,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____2913 with
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
                    let uu____3101 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3101, false))
           | FStar_Parser_AST.PatApp uu____3118 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3140 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3173  ->
                        match uu____3173 with
                        | (loc1,env2,pats1) ->
                            let uu____3205 = aux loc1 env2 pat  in
                            (match uu____3205 with
                             | (loc2,env3,uu____3230,pat1,uu____3232) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3140 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3275 =
                        let uu____3278 =
                          let uu____3283 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3283  in
                        let uu____3284 =
                          let uu____3285 =
                            let uu____3298 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3298, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3285  in
                        FStar_All.pipe_left uu____3278 uu____3284  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3330 =
                               let uu____3331 =
                                 let uu____3344 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3344, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3331  in
                             FStar_All.pipe_left (pos_r r) uu____3330) pats1
                        uu____3275
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
               let uu____3388 =
                 FStar_List.fold_left
                   (fun uu____3428  ->
                      fun p2  ->
                        match uu____3428 with
                        | (loc1,env2,pats) ->
                            let uu____3477 = aux loc1 env2 p2  in
                            (match uu____3477 with
                             | (loc2,env3,uu____3506,pat,uu____3508) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3388 with
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
                    let uu____3603 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____3603 with
                     | (constr,uu____3625) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3628 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3630 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3630, false)))
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
                      (fun uu____3701  ->
                         match uu____3701 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3731  ->
                         match uu____3731 with
                         | (f,uu____3737) ->
                             let uu____3738 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3764  ->
                                       match uu____3764 with
                                       | (g,uu____3770) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____3738 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3775,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____3782 =
                   let uu____3783 =
                     let uu____3790 =
                       let uu____3791 =
                         let uu____3792 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____3792  in
                       FStar_Parser_AST.mk_pattern uu____3791
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____3790, args)  in
                   FStar_Parser_AST.PatApp uu____3783  in
                 FStar_Parser_AST.mk_pattern uu____3782
                   p1.FStar_Parser_AST.prange
                  in
               let uu____3795 = aux loc env1 app  in
               (match uu____3795 with
                | (env2,e,b,p2,uu____3824) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3852 =
                            let uu____3853 =
                              let uu____3866 =
                                let uu___117_3867 = fv  in
                                let uu____3868 =
                                  let uu____3871 =
                                    let uu____3872 =
                                      let uu____3879 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____3879)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3872
                                     in
                                  FStar_Pervasives_Native.Some uu____3871  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___117_3867.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___117_3867.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3868
                                }  in
                              (uu____3866, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____3853  in
                          FStar_All.pipe_left pos uu____3852
                      | uu____3906 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____3956 = aux' true loc env1 p2  in
               (match uu____3956 with
                | (loc1,env2,var,p3,uu____3983) ->
                    let uu____3988 =
                      FStar_List.fold_left
                        (fun uu____4020  ->
                           fun p4  ->
                             match uu____4020 with
                             | (loc2,env3,ps1) ->
                                 let uu____4053 = aux' true loc2 env3 p4  in
                                 (match uu____4053 with
                                  | (loc3,env4,uu____4078,p5,uu____4080) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____3988 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4131 ->
               let uu____4132 = aux' true loc env1 p1  in
               (match uu____4132 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4172 = aux_maybe_or env p  in
         match uu____4172 with
         | (env1,b,pats) ->
             ((let uu____4203 =
                 FStar_List.map
                   (fun pats1  ->
                      check_linear_pattern_variables pats1
                        p.FStar_Parser_AST.prange) pats
                  in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4203);
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
            let uu____4240 =
              let uu____4241 =
                let uu____4246 = FStar_ToSyntax_Env.qualify env x  in
                (uu____4246, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____4241  in
            (env, uu____4240, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4266 =
                  let uu____4267 =
                    let uu____4272 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4272, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4267  in
                mklet uu____4266
            | FStar_Parser_AST.PatVar (x,uu____4274) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4280);
                   FStar_Parser_AST.prange = uu____4281;_},t)
                ->
                let uu____4287 =
                  let uu____4288 =
                    let uu____4293 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____4294 = desugar_term env t  in
                    (uu____4293, uu____4294)  in
                  LetBinder uu____4288  in
                (env, uu____4287, [])
            | uu____4297 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4307 = desugar_data_pat env p is_mut  in
             match uu____4307 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4336;
                       FStar_Syntax_Syntax.p = uu____4337;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4342;
                       FStar_Syntax_Syntax.p = uu____4343;_}::[] -> []
                   | uu____4348 -> p1  in
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
  fun uu____4355  ->
    fun env  ->
      fun pat  ->
        let uu____4358 = desugar_data_pat env pat false  in
        match uu____4358 with | (env1,uu____4374,pat1) -> (env1, pat1)

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
      fun uu____4392  ->
        fun range  ->
          match uu____4392 with
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
              ((let uu____4402 =
                  let uu____4403 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4403  in
                if uu____4402
                then
                  let uu____4404 =
                    let uu____4409 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4409)  in
                  FStar_Errors.log_issue range uu____4404
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
                  let uu____4417 = FStar_ToSyntax_Env.try_lookup_lid env lid
                     in
                  match uu____4417 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4427) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             FStar_Ident.lid_of_path
                               (FStar_Ident.path_of_text private_intro_nm)
                               range
                              in
                           let private_fv =
                             let uu____4437 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4437 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___118_4438 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___118_4438.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___118_4438.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4439 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4446 =
                        let uu____4451 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4451)
                         in
                      FStar_Errors.raise_error uu____4446 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4467 =
                  let uu____4470 =
                    let uu____4471 =
                      let uu____4486 =
                        let uu____4495 =
                          let uu____4502 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4502)  in
                        [uu____4495]  in
                      (lid1, uu____4486)  in
                    FStar_Syntax_Syntax.Tm_app uu____4471  in
                  FStar_Syntax_Syntax.mk uu____4470  in
                uu____4467 FStar_Pervasives_Native.None range))

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
            let uu____4541 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid_with_attributes
                  else
                    FStar_ToSyntax_Env.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4541 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____4587;
                              FStar_Syntax_Syntax.vars = uu____4588;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____4611 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4611 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____4619 =
                                 let uu____4620 =
                                   let uu____4623 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____4623  in
                                 uu____4620.FStar_Syntax_Syntax.n  in
                               match uu____4619 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____4639))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____4640 -> msg
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
                             let uu____4644 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4644 " is deprecated"  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____4645 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____4650 =
                      let uu____4651 =
                        let uu____4658 = mk_ref_read tm1  in
                        (uu____4658,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____4651  in
                    FStar_All.pipe_left mk1 uu____4650
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4674 =
          let uu____4675 = unparen t  in uu____4675.FStar_Parser_AST.tm  in
        match uu____4674 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4676; FStar_Ident.ident = uu____4677;
              FStar_Ident.nsstr = uu____4678; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4681 ->
            let uu____4682 =
              let uu____4687 =
                let uu____4688 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____4688  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____4687)  in
            FStar_Errors.raise_error uu____4682 t.FStar_Parser_AST.range
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
          let uu___119_4708 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___119_4708.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___119_4708.FStar_Syntax_Syntax.vars)
          }  in
        let uu____4711 =
          let uu____4712 = unparen top  in uu____4712.FStar_Parser_AST.tm  in
        match uu____4711 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4713 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____4764::uu____4765::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4769 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____4769 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4782;_},t1::t2::[])
                  ->
                  let uu____4787 = flatten1 t1  in
                  FStar_List.append uu____4787 [t2]
              | uu____4790 -> [t]  in
            let targs =
              let uu____4794 =
                let uu____4797 = unparen top  in flatten1 uu____4797  in
              FStar_All.pipe_right uu____4794
                (FStar_List.map
                   (fun t  ->
                      let uu____4805 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____4805))
               in
            let uu____4806 =
              let uu____4811 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4811
               in
            (match uu____4806 with
             | (tup,uu____4817) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4821 =
              let uu____4824 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              FStar_Pervasives_Native.fst uu____4824  in
            FStar_All.pipe_left setpos uu____4821
        | FStar_Parser_AST.Uvar u ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedUniverseVariable,
                (Prims.strcat "Unexpected universe variable "
                   (Prims.strcat (FStar_Ident.text_of_id u)
                      " in non-universe context")))
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4844 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____4844 with
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
                             let uu____4876 = desugar_term env t  in
                             (uu____4876, FStar_Pervasives_Native.None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4890)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4905 =
              let uu___120_4906 = top  in
              let uu____4907 =
                let uu____4908 =
                  let uu____4915 =
                    let uu___121_4916 = top  in
                    let uu____4917 =
                      let uu____4918 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4918  in
                    {
                      FStar_Parser_AST.tm = uu____4917;
                      FStar_Parser_AST.range =
                        (uu___121_4916.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___121_4916.FStar_Parser_AST.level)
                    }  in
                  (uu____4915, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4908  in
              {
                FStar_Parser_AST.tm = uu____4907;
                FStar_Parser_AST.range =
                  (uu___120_4906.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___120_4906.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4905
        | FStar_Parser_AST.Construct (n1,(a,uu____4921)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____4937 =
                let uu___122_4938 = top  in
                let uu____4939 =
                  let uu____4940 =
                    let uu____4947 =
                      let uu___123_4948 = top  in
                      let uu____4949 =
                        let uu____4950 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____4950  in
                      {
                        FStar_Parser_AST.tm = uu____4949;
                        FStar_Parser_AST.range =
                          (uu___123_4948.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___123_4948.FStar_Parser_AST.level)
                      }  in
                    (uu____4947, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____4940  in
                {
                  FStar_Parser_AST.tm = uu____4939;
                  FStar_Parser_AST.range =
                    (uu___122_4938.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___122_4938.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____4937))
        | FStar_Parser_AST.Construct (n1,(a,uu____4953)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4968 =
              let uu___124_4969 = top  in
              let uu____4970 =
                let uu____4971 =
                  let uu____4978 =
                    let uu___125_4979 = top  in
                    let uu____4980 =
                      let uu____4981 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4981  in
                    {
                      FStar_Parser_AST.tm = uu____4980;
                      FStar_Parser_AST.range =
                        (uu___125_4979.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___125_4979.FStar_Parser_AST.level)
                    }  in
                  (uu____4978, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4971  in
              {
                FStar_Parser_AST.tm = uu____4970;
                FStar_Parser_AST.range =
                  (uu___124_4969.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___124_4969.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4968
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4982; FStar_Ident.ident = uu____4983;
              FStar_Ident.nsstr = uu____4984; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4987; FStar_Ident.ident = uu____4988;
              FStar_Ident.nsstr = uu____4989; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4992; FStar_Ident.ident = uu____4993;
               FStar_Ident.nsstr = uu____4994; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5012 =
              let uu____5013 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____5013  in
            mk1 uu____5012
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5014; FStar_Ident.ident = uu____5015;
              FStar_Ident.nsstr = uu____5016; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5019; FStar_Ident.ident = uu____5020;
              FStar_Ident.nsstr = uu____5021; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5024; FStar_Ident.ident = uu____5025;
              FStar_Ident.nsstr = uu____5026; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5031;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5033 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
              match uu____5033 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____5038 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____5038))
        | FStar_Parser_AST.Var l ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Name l ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____5053 = FStar_ToSyntax_Env.try_lookup_datacon env l
                   in
                match uu____5053 with
                | FStar_Pervasives_Native.Some uu____5062 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5067 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l
                       in
                    (match uu____5067 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5081 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5094 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____5094
              | uu____5095 ->
                  let uu____5102 =
                    let uu____5107 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____5107)  in
                  FStar_Errors.raise_error uu____5102
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____5110 = FStar_ToSyntax_Env.try_lookup_datacon env lid
                 in
              match uu____5110 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5113 =
                    let uu____5118 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____5118)
                     in
                  FStar_Errors.raise_error uu____5113
                    top.FStar_Parser_AST.range
              | uu____5119 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____5138 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____5138 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____5142 =
                    let uu____5149 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                       in
                    (uu____5149, true)  in
                  (match uu____5142 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5164 ->
                            let uu____5171 =
                              FStar_Util.take
                                (fun uu____5195  ->
                                   match uu____5195 with
                                   | (uu____5200,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args
                               in
                            (match uu____5171 with
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
                                     (fun uu____5264  ->
                                        match uu____5264 with
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
                    let uu____5311 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l  in
                    match uu____5311 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____5318 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5325 =
              FStar_List.fold_left
                (fun uu____5370  ->
                   fun b  ->
                     match uu____5370 with
                     | (env1,tparams,typs) ->
                         let uu____5427 = desugar_binder env1 b  in
                         (match uu____5427 with
                          | (xopt,t1) ->
                              let uu____5456 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5465 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____5465)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____5456 with
                               | (env2,x) ->
                                   let uu____5485 =
                                     let uu____5488 =
                                       let uu____5491 =
                                         let uu____5492 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5492
                                          in
                                       [uu____5491]  in
                                     FStar_List.append typs uu____5488  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___126_5518 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___126_5518.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___126_5518.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5485)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____5325 with
             | (env1,uu____5542,targs) ->
                 let uu____5564 =
                   let uu____5569 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5569
                    in
                 (match uu____5564 with
                  | (tup,uu____5575) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5586 = uncurry binders t  in
            (match uu____5586 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___92_5618 =
                   match uu___92_5618 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____5632 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____5632
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____5654 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____5654 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5669 = desugar_binder env b  in
            (match uu____5669 with
             | (FStar_Pervasives_Native.None ,uu____5676) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5686 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____5686 with
                  | ((x,uu____5692),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____5699 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____5699))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____5719 =
              FStar_List.fold_left
                (fun uu____5739  ->
                   fun pat  ->
                     match uu____5739 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5765,t) ->
                              let uu____5767 =
                                let uu____5770 = free_type_vars env1 t  in
                                FStar_List.append uu____5770 ftvs  in
                              (env1, uu____5767)
                          | uu____5775 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____5719 with
             | (uu____5780,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____5792 =
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
                   FStar_List.append uu____5792 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___93_5833 =
                   match uu___93_5833 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5871 =
                                 let uu____5872 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____5872
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____5871 body1  in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1  in
                       let uu____5925 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____5925
                   | p::rest ->
                       let uu____5936 = desugar_binding_pat env1 p  in
                       (match uu____5936 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5960 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____5965 =
                              match b with
                              | LetBinder uu____5998 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____6048) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6084 =
                                          let uu____6089 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____6089, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____6084
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6125,uu____6126) ->
                                             let tup2 =
                                               let uu____6128 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6128
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6132 =
                                                 let uu____6135 =
                                                   let uu____6136 =
                                                     let uu____6151 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____6154 =
                                                       let uu____6157 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____6158 =
                                                         let uu____6161 =
                                                           let uu____6162 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6162
                                                            in
                                                         [uu____6161]  in
                                                       uu____6157 ::
                                                         uu____6158
                                                        in
                                                     (uu____6151, uu____6154)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6136
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6135
                                                  in
                                               uu____6132
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____6173 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6173
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6204,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6206,pats)) ->
                                             let tupn =
                                               let uu____6245 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6245
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6255 =
                                                 let uu____6256 =
                                                   let uu____6271 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____6274 =
                                                     let uu____6283 =
                                                       let uu____6292 =
                                                         let uu____6293 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6293
                                                          in
                                                       [uu____6292]  in
                                                     FStar_List.append args
                                                       uu____6283
                                                      in
                                                   (uu____6271, uu____6274)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6256
                                                  in
                                               mk1 uu____6255  in
                                             let p2 =
                                               let uu____6313 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6313
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6348 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____5965 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6415,uu____6416,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6430 =
                let uu____6431 = unparen e  in uu____6431.FStar_Parser_AST.tm
                 in
              match uu____6430 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____6437 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____6441 ->
            let rec aux args e =
              let uu____6473 =
                let uu____6474 = unparen e  in uu____6474.FStar_Parser_AST.tm
                 in
              match uu____6473 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6487 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6487  in
                  aux (arg :: args) e1
              | uu____6500 ->
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
            let uu____6528 =
              FStar_ToSyntax_Env.resolve_to_fully_qualified_name env bind_lid
               in
            (match uu____6528 with
             | FStar_Pervasives_Native.Some flid when
                 FStar_Ident.lid_equals flid tac_bind_lid ->
                 let r =
                   FStar_Parser_AST.mk_term
                     (FStar_Parser_AST.Const
                        (FStar_Const.Const_range (t2.FStar_Parser_AST.range)))
                     t2.FStar_Parser_AST.range FStar_Parser_AST.Expr
                    in
                 let uu____6533 =
                   FStar_Parser_AST.mkExplicitApp bind1 [r; t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6533
             | uu____6534 ->
                 let uu____6537 =
                   FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6537)
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6540 =
              let uu____6541 =
                let uu____6548 =
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
                (uu____6548,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____6541  in
            mk1 uu____6540
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            let uu____6600 =
              let uu____6605 = FStar_ToSyntax_Env.expect_typ env1  in
              if uu____6605 then desugar_typ else desugar_term  in
            uu____6600 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____6648 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6773  ->
                        match uu____6773 with
                        | (attr_opt,(p,def)) ->
                            let uu____6825 = is_app_pattern p  in
                            if uu____6825
                            then
                              let uu____6850 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____6850, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6914 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____6914, def1)
                               | uu____6947 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____6979);
                                           FStar_Parser_AST.prange =
                                             uu____6980;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____7010 =
                                            let uu____7025 =
                                              let uu____7030 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7030  in
                                            (uu____7025, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____7010, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____7085) ->
                                        if top_level
                                        then
                                          let uu____7114 =
                                            let uu____7129 =
                                              let uu____7134 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7134  in
                                            (uu____7129, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____7114, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____7188 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____7213 =
                FStar_List.fold_left
                  (fun uu____7280  ->
                     fun uu____7281  ->
                       match (uu____7280, uu____7281) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____7377,uu____7378),uu____7379))
                           ->
                           let uu____7472 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7498 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____7498 with
                                  | (env2,xx) ->
                                      let uu____7517 =
                                        let uu____7520 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____7520 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____7517))
                             | FStar_Util.Inr l ->
                                 let uu____7528 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____7528, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____7472 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____7213 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____7660 =
                    match uu____7660 with
                    | (attrs_opt,(uu____7690,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7742 = is_comp_type env1 t  in
                                if uu____7742
                                then
                                  ((let uu____7744 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7754 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____7754))
                                       in
                                    match uu____7744 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____7757 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7759 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____7759))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____7757
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____7763 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7763 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7767 ->
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
                              let uu____7782 =
                                let uu____7783 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7783
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____7782
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
                  let uu____7837 =
                    let uu____7838 =
                      let uu____7851 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs1), uu____7851)  in
                    FStar_Syntax_Syntax.Tm_let uu____7838  in
                  FStar_All.pipe_left mk1 uu____7837
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
              let uu____7905 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____7905 with
              | (env1,binder,pat1) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____7932 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7932
                            FStar_Pervasives_Native.None
                           in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [mk_lb (attrs, (FStar_Util.Inr fv), t, t12)]),
                               body1))
                    | LocalBinder (x,uu____7952) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat1 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7955;
                              FStar_Syntax_Syntax.p = uu____7956;_}::[] ->
                              body1
                          | uu____7961 ->
                              let uu____7964 =
                                let uu____7967 =
                                  let uu____7968 =
                                    let uu____7991 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____7992 =
                                      desugar_disjunctive_pattern pat1
                                        FStar_Pervasives_Native.None body1
                                       in
                                    (uu____7991, uu____7992)  in
                                  FStar_Syntax_Syntax.Tm_match uu____7968  in
                                FStar_Syntax_Syntax.mk uu____7967  in
                              uu____7964 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range
                           in
                        let uu____8002 =
                          let uu____8003 =
                            let uu____8016 =
                              let uu____8017 =
                                let uu____8018 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____8018]  in
                              FStar_Syntax_Subst.close uu____8017 body2  in
                            ((false,
                               [mk_lb
                                  (attrs, (FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____8016)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____8003  in
                        FStar_All.pipe_left mk1 uu____8002
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
            let uu____8046 = FStar_List.hd lbs  in
            (match uu____8046 with
             | (attrs,(head_pat,defn)) ->
                 let uu____8086 = is_rec || (is_app_pattern head_pat)  in
                 if uu____8086
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____8095 =
                let uu____8096 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____8096  in
              mk1 uu____8095  in
            let uu____8097 =
              let uu____8098 =
                let uu____8121 =
                  let uu____8124 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____8124
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None)
                   in
                let uu____8145 =
                  let uu____8160 =
                    let uu____8173 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range
                       in
                    let uu____8176 = desugar_term env t2  in
                    (uu____8173, FStar_Pervasives_Native.None, uu____8176)
                     in
                  let uu____8185 =
                    let uu____8200 =
                      let uu____8213 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range
                         in
                      let uu____8216 = desugar_term env t3  in
                      (uu____8213, FStar_Pervasives_Native.None, uu____8216)
                       in
                    [uu____8200]  in
                  uu____8160 :: uu____8185  in
                (uu____8121, uu____8145)  in
              FStar_Syntax_Syntax.Tm_match uu____8098  in
            mk1 uu____8097
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
            let desugar_branch uu____8357 =
              match uu____8357 with
              | (pat,wopt,b) ->
                  let uu____8375 = desugar_match_pat env pat  in
                  (match uu____8375 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8396 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____8396
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____8398 =
              let uu____8399 =
                let uu____8422 = desugar_term env e  in
                let uu____8423 = FStar_List.collect desugar_branch branches
                   in
                (uu____8422, uu____8423)  in
              FStar_Syntax_Syntax.Tm_match uu____8399  in
            FStar_All.pipe_left mk1 uu____8398
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8452 = is_comp_type env t  in
              if uu____8452
              then
                let uu____8459 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____8459
              else
                (let uu____8465 = desugar_term env t  in
                 FStar_Util.Inl uu____8465)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____8471 =
              let uu____8472 =
                let uu____8499 = desugar_term env e  in
                (uu____8499, (annot, tac_opt1), FStar_Pervasives_Native.None)
                 in
              FStar_Syntax_Syntax.Tm_ascribed uu____8472  in
            FStar_All.pipe_left mk1 uu____8471
        | FStar_Parser_AST.Record (uu____8524,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____8561 = FStar_List.hd fields  in
              match uu____8561 with | (f,uu____8573) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8615  ->
                        match uu____8615 with
                        | (g,uu____8621) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____8627,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8641 =
                         let uu____8646 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____8646)
                          in
                       FStar_Errors.raise_error uu____8641
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
                  let uu____8654 =
                    let uu____8665 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8696  ->
                              match uu____8696 with
                              | (f,uu____8706) ->
                                  let uu____8707 =
                                    let uu____8708 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8708
                                     in
                                  (uu____8707, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____8665)  in
                  FStar_Parser_AST.Construct uu____8654
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____8726 =
                      let uu____8727 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____8727  in
                    FStar_Parser_AST.mk_term uu____8726 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____8729 =
                      let uu____8742 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8772  ->
                                match uu____8772 with
                                | (f,uu____8782) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____8742)  in
                    FStar_Parser_AST.Record uu____8729  in
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
                         FStar_Syntax_Syntax.pos = uu____8844;
                         FStar_Syntax_Syntax.vars = uu____8845;_},args);
                    FStar_Syntax_Syntax.pos = uu____8847;
                    FStar_Syntax_Syntax.vars = uu____8848;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8876 =
                     let uu____8877 =
                       let uu____8892 =
                         let uu____8893 =
                           let uu____8896 =
                             let uu____8897 =
                               let uu____8904 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____8904)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____8897  in
                           FStar_Pervasives_Native.Some uu____8896  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____8893
                          in
                       (uu____8892, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____8877  in
                   FStar_All.pipe_left mk1 uu____8876  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8935 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8939 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
                 in
              match uu____8939 with
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
                  let uu____8958 =
                    let uu____8959 =
                      let uu____8974 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual
                         in
                      let uu____8975 =
                        let uu____8978 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____8978]  in
                      (uu____8974, uu____8975)  in
                    FStar_Syntax_Syntax.Tm_app uu____8959  in
                  FStar_All.pipe_left mk1 uu____8958))
        | FStar_Parser_AST.NamedTyp (uu____8983,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | uu____8986 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8987 ->
            let uu____8988 =
              let uu____8993 =
                let uu____8994 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term" uu____8994  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____8993)  in
            FStar_Errors.raise_error uu____8988 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8996 -> false
    | uu____9005 -> true

and (is_synth_by_tactic :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____9011 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid  in
          (match uu____9011 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____9015 -> false

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
           (fun uu____9052  ->
              match uu____9052 with
              | (a,imp) ->
                  let uu____9065 = desugar_term env a  in
                  arg_withimp_e imp uu____9065))

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
        let is_requires uu____9091 =
          match uu____9091 with
          | (t1,uu____9097) ->
              let uu____9098 =
                let uu____9099 = unparen t1  in
                uu____9099.FStar_Parser_AST.tm  in
              (match uu____9098 with
               | FStar_Parser_AST.Requires uu____9100 -> true
               | uu____9107 -> false)
           in
        let is_ensures uu____9115 =
          match uu____9115 with
          | (t1,uu____9121) ->
              let uu____9122 =
                let uu____9123 = unparen t1  in
                uu____9123.FStar_Parser_AST.tm  in
              (match uu____9122 with
               | FStar_Parser_AST.Ensures uu____9124 -> true
               | uu____9131 -> false)
           in
        let is_app head1 uu____9142 =
          match uu____9142 with
          | (t1,uu____9148) ->
              let uu____9149 =
                let uu____9150 = unparen t1  in
                uu____9150.FStar_Parser_AST.tm  in
              (match uu____9149 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____9152;
                      FStar_Parser_AST.level = uu____9153;_},uu____9154,uu____9155)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____9156 -> false)
           in
        let is_smt_pat uu____9164 =
          match uu____9164 with
          | (t1,uu____9170) ->
              let uu____9171 =
                let uu____9172 = unparen t1  in
                uu____9172.FStar_Parser_AST.tm  in
              (match uu____9171 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____9175);
                             FStar_Parser_AST.range = uu____9176;
                             FStar_Parser_AST.level = uu____9177;_},uu____9178)::uu____9179::[])
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
                             FStar_Parser_AST.range = uu____9218;
                             FStar_Parser_AST.level = uu____9219;_},uu____9220)::uu____9221::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____9246 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____9274 = head_and_args t1  in
          match uu____9274 with
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
                   let thunk_ens uu____9368 =
                     match uu____9368 with
                     | (e,i) ->
                         let uu____9379 = thunk_ens_ e  in (uu____9379, i)
                      in
                   let fail_lemma uu____9389 =
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
                         let uu____9469 =
                           let uu____9476 =
                             let uu____9483 = thunk_ens ens  in
                             [uu____9483; nil_pat]  in
                           req_true :: uu____9476  in
                         unit_tm :: uu____9469
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____9530 =
                           let uu____9537 =
                             let uu____9544 = thunk_ens ens  in
                             [uu____9544; nil_pat]  in
                           req :: uu____9537  in
                         unit_tm :: uu____9530
                     | ens::smtpat::[] when
                         (((let uu____9593 = is_requires ens  in
                            Prims.op_Negation uu____9593) &&
                             (let uu____9595 = is_smt_pat ens  in
                              Prims.op_Negation uu____9595))
                            &&
                            (let uu____9597 = is_decreases ens  in
                             Prims.op_Negation uu____9597))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____9598 =
                           let uu____9605 =
                             let uu____9612 = thunk_ens ens  in
                             [uu____9612; smtpat]  in
                           req_true :: uu____9605  in
                         unit_tm :: uu____9598
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____9659 =
                           let uu____9666 =
                             let uu____9673 = thunk_ens ens  in
                             [uu____9673; nil_pat; dec]  in
                           req_true :: uu____9666  in
                         unit_tm :: uu____9659
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9733 =
                           let uu____9740 =
                             let uu____9747 = thunk_ens ens  in
                             [uu____9747; smtpat; dec]  in
                           req_true :: uu____9740  in
                         unit_tm :: uu____9733
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____9807 =
                           let uu____9814 =
                             let uu____9821 = thunk_ens ens  in
                             [uu____9821; nil_pat; dec]  in
                           req :: uu____9814  in
                         unit_tm :: uu____9807
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9881 =
                           let uu____9888 =
                             let uu____9895 = thunk_ens ens  in
                             [uu____9895; smtpat]  in
                           req :: uu____9888  in
                         unit_tm :: uu____9881
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____9960 =
                           let uu____9967 =
                             let uu____9974 = thunk_ens ens  in
                             [uu____9974; dec; smtpat]  in
                           req :: uu____9967  in
                         unit_tm :: uu____9960
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____10036 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____10036, args)
               | FStar_Parser_AST.Name l when
                   (let uu____10064 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____10064
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____10082 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____10082
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
               | uu____10120 ->
                   let default_effect =
                     let uu____10122 = FStar_Options.ml_ish ()  in
                     if uu____10122
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____10125 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____10125
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
        let uu____10149 = pre_process_comp_typ t  in
        match uu____10149 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____10198 =
                       let uu____10203 =
                         let uu____10204 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____10204
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____10203)
                        in
                     fail () uu____10198)
                else Obj.repr ());
             (let is_universe uu____10213 =
                match uu____10213 with
                | (uu____10218,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____10220 = FStar_Util.take is_universe args  in
              match uu____10220 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____10279  ->
                         match uu____10279 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____10286 =
                    let uu____10301 = FStar_List.hd args1  in
                    let uu____10310 = FStar_List.tl args1  in
                    (uu____10301, uu____10310)  in
                  (match uu____10286 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____10365 =
                         let is_decrease uu____10401 =
                           match uu____10401 with
                           | (t1,uu____10411) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____10421;
                                       FStar_Syntax_Syntax.vars = uu____10422;_},uu____10423::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10454 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____10365 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10568  ->
                                      match uu____10568 with
                                      | (t1,uu____10578) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10587,(arg,uu____10589)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10618 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____10631 -> false  in
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
                                           | uu____10771 -> pat  in
                                         let uu____10772 =
                                           let uu____10783 =
                                             let uu____10794 =
                                               let uu____10803 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____10803, aq)  in
                                             [uu____10794]  in
                                           ens :: uu____10783  in
                                         req :: uu____10772
                                     | uu____10844 -> rest2
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
        | uu____10866 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___127_10883 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___127_10883.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___127_10883.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___128_10917 = b  in
             {
               FStar_Parser_AST.b = (uu___128_10917.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___128_10917.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___128_10917.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10976 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10976)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10989 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____10989 with
             | (env1,a1) ->
                 let a2 =
                   let uu___129_10999 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___129_10999.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___129_10999.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____11021 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____11035 =
                     let uu____11038 =
                       let uu____11039 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____11039]  in
                     no_annot_abs uu____11038 body2  in
                   FStar_All.pipe_left setpos uu____11035  in
                 let uu____11044 =
                   let uu____11045 =
                     let uu____11060 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____11061 =
                       let uu____11064 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____11064]  in
                     (uu____11060, uu____11061)  in
                   FStar_Syntax_Syntax.Tm_app uu____11045  in
                 FStar_All.pipe_left mk1 uu____11044)
        | uu____11069 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____11141 = q (rest, pats, body)  in
              let uu____11148 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____11141 uu____11148
                FStar_Parser_AST.Formula
               in
            let uu____11149 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____11149 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____11158 -> failwith "impossible"  in
      let uu____11161 =
        let uu____11162 = unparen f  in uu____11162.FStar_Parser_AST.tm  in
      match uu____11161 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____11169,uu____11170) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____11181,uu____11182) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11213 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____11213
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11249 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____11249
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____11292 -> desugar_term env f

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
      let uu____11297 =
        FStar_List.fold_left
          (fun uu____11333  ->
             fun b  ->
               match uu____11333 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___130_11385 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___130_11385.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___130_11385.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___130_11385.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11402 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____11402 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___131_11422 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_11422.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_11422.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11439 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____11297 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____11526 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11526)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11531 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11531)
      | FStar_Parser_AST.TVariable x ->
          let uu____11535 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____11535)
      | FStar_Parser_AST.NoName t ->
          let uu____11543 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____11543)
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
               (fun uu___94_11576  ->
                  match uu___94_11576 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11577 -> false))
           in
        let quals2 q =
          let uu____11588 =
            (let uu____11591 = FStar_ToSyntax_Env.iface env  in
             Prims.op_Negation uu____11591) ||
              (FStar_ToSyntax_Env.admitted_iface env)
             in
          if uu____11588
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____11604 =
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
                  FStar_Syntax_Syntax.sigquals = uu____11604;
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
            let uu____11635 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11665  ->
                        match uu____11665 with
                        | (x,uu____11673) ->
                            let uu____11674 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____11674 with
                             | (field_name,uu____11682) ->
                                 let only_decl =
                                   ((let uu____11686 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11686)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11688 =
                                        let uu____11689 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____11689.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____11688)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11703 =
                                       FStar_List.filter
                                         (fun uu___95_11707  ->
                                            match uu___95_11707 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11708 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11703
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___96_11721  ->
                                             match uu___96_11721 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11722 -> false))
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
                                      let uu____11730 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____11730
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____11735 =
                                        let uu____11740 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____11740  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11735;
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
                                      let uu____11744 =
                                        let uu____11745 =
                                          let uu____11752 =
                                            let uu____11755 =
                                              let uu____11756 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____11756
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____11755]  in
                                          ((false, [lb]), uu____11752)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11745
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11744;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____11635 FStar_List.flatten
  
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
            (lid,uu____11800,t,uu____11802,n1,uu____11804) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11809 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____11809 with
             | (formals,uu____11825) ->
                 (match formals with
                  | [] -> []
                  | uu____11848 ->
                      let filter_records uu___97_11860 =
                        match uu___97_11860 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11863,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11875 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____11877 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____11877 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____11887 = FStar_Util.first_N n1 formals  in
                      (match uu____11887 with
                       | (uu____11910,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11936 -> []
  
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
                    let uu____11986 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____11986
                    then
                      let uu____11989 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____11989
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____11992 =
                      let uu____11997 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____11997  in
                    let uu____11998 =
                      let uu____12001 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____12001  in
                    let uu____12004 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11992;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11998;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____12004;
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
          let tycon_id uu___98_12051 =
            match uu___98_12051 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____12053,uu____12054) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____12064,uu____12065,uu____12066) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____12076,uu____12077,uu____12078) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____12108,uu____12109,uu____12110) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____12152) ->
                let uu____12153 =
                  let uu____12154 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12154  in
                FStar_Parser_AST.mk_term uu____12153 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____12156 =
                  let uu____12157 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12157  in
                FStar_Parser_AST.mk_term uu____12156 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____12159) ->
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
              | uu____12182 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____12188 =
                     let uu____12189 =
                       let uu____12196 = binder_to_term b  in
                       (out, uu____12196, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____12189  in
                   FStar_Parser_AST.mk_term uu____12188
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___99_12206 =
            match uu___99_12206 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____12261  ->
                       match uu____12261 with
                       | (x,t,uu____12272) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____12278 =
                    let uu____12279 =
                      let uu____12280 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____12280  in
                    FStar_Parser_AST.mk_term uu____12279
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____12278 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____12284 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____12311  ->
                          match uu____12311 with
                          | (x,uu____12321,uu____12322) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____12284)
            | uu____12375 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___100_12406 =
            match uu___100_12406 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____12430 = typars_of_binders _env binders  in
                (match uu____12430 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____12476 =
                         let uu____12477 =
                           let uu____12478 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____12478  in
                         FStar_Parser_AST.mk_term uu____12477
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____12476 binders  in
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
            | uu____12491 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____12535 =
              FStar_List.fold_left
                (fun uu____12575  ->
                   fun uu____12576  ->
                     match (uu____12575, uu____12576) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12667 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____12667 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____12535 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12780 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____12780
                | uu____12781 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____12789 = desugar_abstract_tc quals env [] tc  in
              (match uu____12789 with
               | (uu____12802,uu____12803,se,uu____12805) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12808,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12825 =
                                 let uu____12826 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____12826  in
                               if uu____12825
                               then
                                 let uu____12827 =
                                   let uu____12832 =
                                     let uu____12833 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____12833
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____12832)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12827
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
                           | uu____12840 ->
                               let uu____12841 =
                                 let uu____12844 =
                                   let uu____12845 =
                                     let uu____12858 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____12858)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12845
                                    in
                                 FStar_Syntax_Syntax.mk uu____12844  in
                               uu____12841 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___132_12862 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___132_12862.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___132_12862.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___132_12862.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12865 -> failwith "Impossible"  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   let env2 =
                     let uu____12868 = FStar_ToSyntax_Env.qualify env1 id1
                        in
                     FStar_ToSyntax_Env.push_doc env1 uu____12868
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____12883 = typars_of_binders env binders  in
              (match uu____12883 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12919 =
                           FStar_Util.for_some
                             (fun uu___101_12921  ->
                                match uu___101_12921 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12922 -> false) quals
                            in
                         if uu____12919
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____12929 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___102_12933  ->
                               match uu___102_12933 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12934 -> false))
                        in
                     if uu____12929
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_ToSyntax_Env.qualify env id1  in
                   let se =
                     let uu____12943 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____12943
                     then
                       let uu____12946 =
                         let uu____12953 =
                           let uu____12954 = unparen t  in
                           uu____12954.FStar_Parser_AST.tm  in
                         match uu____12953 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12975 =
                               match FStar_List.rev args with
                               | (last_arg,uu____13005)::args_rev ->
                                   let uu____13017 =
                                     let uu____13018 = unparen last_arg  in
                                     uu____13018.FStar_Parser_AST.tm  in
                                   (match uu____13017 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____13046 -> ([], args))
                               | uu____13055 -> ([], args)  in
                             (match uu____12975 with
                              | (cattributes,args1) ->
                                  let uu____13094 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____13094))
                         | uu____13105 -> (t, [])  in
                       match uu____12946 with
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
                                  (fun uu___103_13127  ->
                                     match uu___103_13127 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____13128 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____13139)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____13163 = tycon_record_as_variant trec  in
              (match uu____13163 with
               | (t,fs) ->
                   let uu____13180 =
                     let uu____13183 =
                       let uu____13184 =
                         let uu____13193 =
                           let uu____13196 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____13196  in
                         (uu____13193, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____13184  in
                     uu____13183 :: quals  in
                   desugar_tycon env d uu____13180 [t])
          | uu____13201::uu____13202 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____13363 = et  in
                match uu____13363 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13588 ->
                         let trec = tc  in
                         let uu____13612 = tycon_record_as_variant trec  in
                         (match uu____13612 with
                          | (t,fs) ->
                              let uu____13671 =
                                let uu____13674 =
                                  let uu____13675 =
                                    let uu____13684 =
                                      let uu____13687 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____13687  in
                                    (uu____13684, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____13675
                                   in
                                uu____13674 :: quals1  in
                              collect_tcs uu____13671 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____13774 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____13774 with
                          | (env2,uu____13834,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____13983 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____13983 with
                          | (env2,uu____14043,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____14168 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____14215 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____14215 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___105_14726  ->
                             match uu___105_14726 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____14793,uu____14794);
                                    FStar_Syntax_Syntax.sigrng = uu____14795;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14796;
                                    FStar_Syntax_Syntax.sigmeta = uu____14797;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14798;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14859 =
                                     typars_of_binders env1 binders  in
                                   match uu____14859 with
                                   | (env2,tpars1) ->
                                       let uu____14890 =
                                         push_tparams env2 tpars1  in
                                       (match uu____14890 with
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
                                 let uu____14923 =
                                   let uu____14944 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____14944)
                                    in
                                 [uu____14923]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____15012);
                                    FStar_Syntax_Syntax.sigrng = uu____15013;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____15015;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____15016;_},constrs,tconstr,quals1)
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
                                 let uu____15112 = push_tparams env1 tpars
                                    in
                                 (match uu____15112 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____15189  ->
                                             match uu____15189 with
                                             | (x,uu____15203) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____15211 =
                                        let uu____15240 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____15354  ->
                                                  match uu____15354 with
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
                                                        let uu____15410 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____15410
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
                                                                uu___104_15421
                                                                 ->
                                                                match uu___104_15421
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15433
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____15441 =
                                                        let uu____15462 =
                                                          let uu____15463 =
                                                            let uu____15464 =
                                                              let uu____15479
                                                                =
                                                                let uu____15482
                                                                  =
                                                                  let uu____15485
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15485
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15482
                                                                 in
                                                              (name, univs1,
                                                                uu____15479,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15464
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15463;
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
                                                          uu____15462)
                                                         in
                                                      (name, uu____15441)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____15240
                                         in
                                      (match uu____15211 with
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
                             | uu____15724 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15856  ->
                             match uu____15856 with
                             | (name_doc,uu____15884,uu____15885) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15965  ->
                             match uu____15965 with
                             | (uu____15986,uu____15987,se) -> se))
                      in
                   let uu____16017 =
                     let uu____16024 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____16024 rng
                      in
                   (match uu____16017 with
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
                               (fun uu____16090  ->
                                  match uu____16090 with
                                  | (uu____16113,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____16164,tps,k,uu____16167,constrs)
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
                                  | uu____16186 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____16203  ->
                                 match uu____16203 with
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
      let uu____16238 =
        FStar_List.fold_left
          (fun uu____16261  ->
             fun b  ->
               match uu____16261 with
               | (env1,binders1) ->
                   let uu____16281 = desugar_binder env1 b  in
                   (match uu____16281 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16298 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____16298 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____16315 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____16238 with
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
          let uu____16360 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___106_16365  ->
                    match uu___106_16365 with
                    | FStar_Syntax_Syntax.Reflectable uu____16366 -> true
                    | uu____16367 -> false))
             in
          if uu____16360
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
                let uu____16466 = desugar_binders monad_env eff_binders  in
                match uu____16466 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____16487 =
                        let uu____16488 =
                          let uu____16495 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          FStar_Pervasives_Native.fst uu____16495  in
                        FStar_List.length uu____16488  in
                      uu____16487 = (Prims.parse_int "1")  in
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
                          (uu____16537,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16539,uu____16540,uu____16541),uu____16542)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16575 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____16576 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16588 = name_of_eff_decl decl  in
                           FStar_List.mem uu____16588 mandatory_members)
                        eff_decls
                       in
                    (match uu____16576 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16605 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16634  ->
                                   fun decl  ->
                                     match uu____16634 with
                                     | (env2,out) ->
                                         let uu____16654 =
                                           desugar_decl env2 decl  in
                                         (match uu____16654 with
                                          | (env3,ses) ->
                                              let uu____16667 =
                                                let uu____16670 =
                                                  FStar_List.hd ses  in
                                                uu____16670 :: out  in
                                              (env3, uu____16667)))
                                (env1, []))
                            in
                         (match uu____16605 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16738,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16741,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16742,
                                                                (def,uu____16744)::
                                                                (cps_type,uu____16746)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16747;
                                                             FStar_Parser_AST.level
                                                               = uu____16748;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16800 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16800 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16820 =
                                                   let uu____16821 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____16822 =
                                                     let uu____16823 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16823
                                                      in
                                                   let uu____16828 =
                                                     let uu____16829 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16829
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16821;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16822;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16828
                                                   }  in
                                                 (uu____16820, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16836,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16839,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16874 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16874 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16894 =
                                                   let uu____16895 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____16896 =
                                                     let uu____16897 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16897
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16895;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16896;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____16894, doc1))
                                        | uu____16904 ->
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
                                let uu____16934 =
                                  let uu____16935 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16935
                                   in
                                ([], uu____16934)  in
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
                                    let uu____16952 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____16952)  in
                                  let uu____16959 =
                                    let uu____16960 =
                                      let uu____16961 =
                                        let uu____16962 = lookup "repr"  in
                                        FStar_Pervasives_Native.snd
                                          uu____16962
                                         in
                                      let uu____16971 = lookup "return"  in
                                      let uu____16972 = lookup "bind"  in
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
                                          uu____16961;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16971;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16972;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16960
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16959;
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
                                       (fun uu___107_16976  ->
                                          match uu___107_16976 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16977 -> true
                                          | uu____16978 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____16988 =
                                     let uu____16989 =
                                       let uu____16990 = lookup "return_wp"
                                          in
                                       let uu____16991 = lookup "bind_wp"  in
                                       let uu____16992 =
                                         lookup "if_then_else"  in
                                       let uu____16993 = lookup "ite_wp"  in
                                       let uu____16994 = lookup "stronger"
                                          in
                                       let uu____16995 = lookup "close_wp"
                                          in
                                       let uu____16996 = lookup "assert_p"
                                          in
                                       let uu____16997 = lookup "assume_p"
                                          in
                                       let uu____16998 = lookup "null_wp"  in
                                       let uu____16999 = lookup "trivial"  in
                                       let uu____17000 =
                                         if rr
                                         then
                                           let uu____17001 = lookup "repr"
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____17001
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____17017 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____17019 =
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
                                           uu____16990;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16991;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16992;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16993;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16994;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16995;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16996;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16997;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16998;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16999;
                                         FStar_Syntax_Syntax.repr =
                                           uu____17000;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____17017;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____17019;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16989
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16988;
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
                                        fun uu____17044  ->
                                          match uu____17044 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____17058 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____17058
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
                let uu____17082 = desugar_binders env1 eff_binders  in
                match uu____17082 with
                | (env2,binders) ->
                    let uu____17101 =
                      let uu____17120 = head_and_args defn  in
                      match uu____17120 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____17165 ->
                                let uu____17166 =
                                  let uu____17171 =
                                    let uu____17172 =
                                      let uu____17173 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____17173 " not found"
                                       in
                                    Prims.strcat "Effect " uu____17172  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____17171)
                                   in
                                FStar_Errors.raise_error uu____17166
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____17175 =
                            match FStar_List.rev args with
                            | (last_arg,uu____17205)::args_rev ->
                                let uu____17217 =
                                  let uu____17218 = unparen last_arg  in
                                  uu____17218.FStar_Parser_AST.tm  in
                                (match uu____17217 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____17246 -> ([], args))
                            | uu____17255 -> ([], args)  in
                          (match uu____17175 with
                           | (cattributes,args1) ->
                               let uu____17306 = desugar_args env2 args1  in
                               let uu____17315 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____17306, uu____17315))
                       in
                    (match uu____17101 with
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
                          (let uu____17371 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____17371 with
                           | (ed_binders,uu____17385,ed_binders_opening) ->
                               let sub1 uu____17396 =
                                 match uu____17396 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____17410 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____17410 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____17414 =
                                       let uu____17415 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____17415)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____17414
                                  in
                               let mname =
                                 FStar_ToSyntax_Env.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____17420 =
                                   let uu____17421 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____17421
                                    in
                                 let uu____17432 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____17433 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____17434 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____17435 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____17436 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____17437 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____17438 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____17439 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____17440 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____17441 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____17442 =
                                   let uu____17443 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____17443
                                    in
                                 let uu____17454 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____17455 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____17456 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____17464 =
                                          FStar_ToSyntax_Env.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____17465 =
                                          let uu____17466 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17466
                                           in
                                        let uu____17477 =
                                          let uu____17478 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17478
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____17464;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____17465;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____17477
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
                                     uu____17420;
                                   FStar_Syntax_Syntax.ret_wp = uu____17432;
                                   FStar_Syntax_Syntax.bind_wp = uu____17433;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____17434;
                                   FStar_Syntax_Syntax.ite_wp = uu____17435;
                                   FStar_Syntax_Syntax.stronger = uu____17436;
                                   FStar_Syntax_Syntax.close_wp = uu____17437;
                                   FStar_Syntax_Syntax.assert_p = uu____17438;
                                   FStar_Syntax_Syntax.assume_p = uu____17439;
                                   FStar_Syntax_Syntax.null_wp = uu____17440;
                                   FStar_Syntax_Syntax.trivial = uu____17441;
                                   FStar_Syntax_Syntax.repr = uu____17442;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____17454;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____17455;
                                   FStar_Syntax_Syntax.actions = uu____17456
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____17491 =
                                     let uu____17492 =
                                       let uu____17499 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____17499
                                        in
                                     FStar_List.length uu____17492  in
                                   uu____17491 = (Prims.parse_int "1")  in
                                 let uu____17528 =
                                   let uu____17531 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____17531 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____17528;
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
                                             let uu____17551 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                in
                                             FStar_ToSyntax_Env.push_sigelt
                                               env5 uu____17551
                                              in
                                           FStar_ToSyntax_Env.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____17553 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____17553
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
    let uu____17568 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____17568 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____17619 ->
              let uu____17620 =
                let uu____17621 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____17621
                 in
              Prims.strcat "\n  " uu____17620
          | uu____17622 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____17635  ->
               match uu____17635 with
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
          let uu____17653 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____17653
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____17655 =
          let uu____17664 = FStar_Syntax_Syntax.as_arg arg  in [uu____17664]
           in
        FStar_Syntax_Util.mk_app fv uu____17655

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____17671 = desugar_decl_noattrs env d  in
      match uu____17671 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____17691 = mk_comment_attr d  in uu____17691 :: attrs1  in
          let s =
            FStar_List.fold_left
              (fun s  ->
                 fun a  ->
                   let uu____17702 =
                     let uu____17703 = FStar_Syntax_Print.term_to_string a
                        in
                     Prims.strcat "; " uu____17703  in
                   Prims.strcat s uu____17702) "" attrs2
             in
          let uu____17704 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___133_17710 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___133_17710.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___133_17710.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_17710.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_17710.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____17704)

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
      | FStar_Parser_AST.Fsdoc uu____17736 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17752 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____17752, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____17791  ->
                 match uu____17791 with | (x,uu____17799) -> x) tcs
             in
          let uu____17804 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____17804 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17826;
                    FStar_Parser_AST.prange = uu____17827;_},uu____17828)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17837;
                    FStar_Parser_AST.prange = uu____17838;_},uu____17839)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17854;
                         FStar_Parser_AST.prange = uu____17855;_},uu____17856);
                    FStar_Parser_AST.prange = uu____17857;_},uu____17858)::[]
                   -> false
               | (p,uu____17874)::[] ->
                   let uu____17883 = is_app_pattern p  in
                   Prims.op_Negation uu____17883
               | uu____17884 -> false)
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
            let uu____17958 =
              let uu____17959 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____17959.FStar_Syntax_Syntax.n  in
            (match uu____17958 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17967) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____18000::uu____18001 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____18004 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___108_18018  ->
                               match uu___108_18018 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____18021;
                                   FStar_Syntax_Syntax.lbunivs = uu____18022;
                                   FStar_Syntax_Syntax.lbtyp = uu____18023;
                                   FStar_Syntax_Syntax.lbeff = uu____18024;
                                   FStar_Syntax_Syntax.lbdef = uu____18025;
                                   FStar_Syntax_Syntax.lbattrs = uu____18026;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____18038;
                                   FStar_Syntax_Syntax.lbtyp = uu____18039;
                                   FStar_Syntax_Syntax.lbeff = uu____18040;
                                   FStar_Syntax_Syntax.lbdef = uu____18041;
                                   FStar_Syntax_Syntax.lbattrs = uu____18042;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____18056 =
                     FStar_All.pipe_right lets1
                       (FStar_Util.for_some
                          (fun uu____18087  ->
                             match uu____18087 with
                             | (uu____18100,(uu____18101,t)) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____18056
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____18125 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____18125
                   then
                     let uu____18134 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___134_18148 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___135_18150 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___135_18150.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___135_18150.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___134_18148.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___134_18148.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___134_18148.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___134_18148.FStar_Syntax_Syntax.lbdef);
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___134_18148.FStar_Syntax_Syntax.lbattrs)
                               }))
                        in
                     ((FStar_Pervasives_Native.fst lbs), uu____18134)
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
             | uu____18185 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____18191 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____18210 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____18191 with
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
                       let uu___136_18234 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___136_18234.FStar_Parser_AST.prange)
                       }
                   | uu____18235 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___137_18242 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___137_18242.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___137_18242.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___137_18242.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____18274 id1 =
                   match uu____18274 with
                   | (env1,ses) ->
                       let main =
                         let uu____18295 =
                           let uu____18296 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____18296  in
                         FStar_Parser_AST.mk_term uu____18295
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
                       let uu____18346 = desugar_decl env1 id_decl  in
                       (match uu____18346 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____18364 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____18364 FStar_Util.set_elements
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
            let uu____18395 = close_fun env t  in
            desugar_term env uu____18395  in
          let quals1 =
            let uu____18399 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env)
               in
            if uu____18399
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_ToSyntax_Env.qualify env id1  in
          let se =
            let uu____18405 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____18405;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____18417 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____18417 with
           | (t,uu____18431) ->
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
            let uu____18465 =
              let uu____18472 = FStar_Syntax_Syntax.null_binder t  in
              [uu____18472]  in
            let uu____18473 =
              let uu____18476 =
                let uu____18477 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____18477  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____18476
               in
            FStar_Syntax_Util.arrow uu____18465 uu____18473  in
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
            let uu____18539 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____18539 with
            | FStar_Pervasives_Native.None  ->
                let uu____18542 =
                  let uu____18547 =
                    let uu____18548 =
                      let uu____18549 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____18549 " not found"  in
                    Prims.strcat "Effect name " uu____18548  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____18547)  in
                FStar_Errors.raise_error uu____18542
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____18553 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18595 =
                  let uu____18604 =
                    let uu____18611 = desugar_term env t  in
                    ([], uu____18611)  in
                  FStar_Pervasives_Native.Some uu____18604  in
                (uu____18595, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18644 =
                  let uu____18653 =
                    let uu____18660 = desugar_term env wp  in
                    ([], uu____18660)  in
                  FStar_Pervasives_Native.Some uu____18653  in
                let uu____18669 =
                  let uu____18678 =
                    let uu____18685 = desugar_term env t  in
                    ([], uu____18685)  in
                  FStar_Pervasives_Native.Some uu____18678  in
                (uu____18644, uu____18669)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18711 =
                  let uu____18720 =
                    let uu____18727 = desugar_term env t  in
                    ([], uu____18727)  in
                  FStar_Pervasives_Native.Some uu____18720  in
                (FStar_Pervasives_Native.None, uu____18711)
             in
          (match uu____18553 with
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
      let uu____18815 =
        FStar_List.fold_left
          (fun uu____18835  ->
             fun d  ->
               match uu____18835 with
               | (env1,sigelts) ->
                   let uu____18855 = desugar_decl env1 d  in
                   (match uu____18855 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____18815 with
      | (env1,sigelts) ->
          let rec forward acc uu___110_18896 =
            match uu___110_18896 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18910,FStar_Syntax_Syntax.Sig_let uu____18911) ->
                     let uu____18924 =
                       let uu____18927 =
                         let uu___138_18928 = se2  in
                         let uu____18929 =
                           let uu____18932 =
                             FStar_List.filter
                               (fun uu___109_18946  ->
                                  match uu___109_18946 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____18950;
                                           FStar_Syntax_Syntax.vars =
                                             uu____18951;_},uu____18952);
                                      FStar_Syntax_Syntax.pos = uu____18953;
                                      FStar_Syntax_Syntax.vars = uu____18954;_}
                                      when
                                      let uu____18977 =
                                        let uu____18978 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____18978
                                         in
                                      uu____18977 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____18979 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____18932
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___138_18928.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___138_18928.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___138_18928.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___138_18928.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____18929
                         }  in
                       uu____18927 :: se1 :: acc  in
                     forward uu____18924 sigelts1
                 | uu____18984 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____18992 = forward [] sigelts  in (env1, uu____18992)
  
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
          | (FStar_Pervasives_Native.None ,uu____19043) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____19047;
               FStar_Syntax_Syntax.exports = uu____19048;
               FStar_Syntax_Syntax.is_interface = uu____19049;_},FStar_Parser_AST.Module
             (current_lid,uu____19051)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____19059) ->
              let uu____19062 =
                FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____19062
           in
        let uu____19067 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____19103 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname FStar_ToSyntax_Env.default_mii
                 in
              (uu____19103, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____19120 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname FStar_ToSyntax_Env.default_mii
                 in
              (uu____19120, mname, decls, false)
           in
        match uu____19067 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____19150 = desugar_decls env2 decls  in
            (match uu____19150 with
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
          let uu____19204 =
            (FStar_Options.interactive ()) &&
              (let uu____19206 =
                 let uu____19207 =
                   let uu____19208 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____19208  in
                 FStar_Util.get_file_extension uu____19207  in
               FStar_List.mem uu____19206 ["fsti"; "fsi"])
             in
          if uu____19204 then as_interface m else m  in
        let uu____19212 = desugar_modul_common curmod env m1  in
        match uu____19212 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____19227 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____19243 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____19243 with
      | (env1,modul,pop_when_done) ->
          let uu____19257 =
            FStar_ToSyntax_Env.finish_module_or_interface env1 modul  in
          (match uu____19257 with
           | (env2,modul1) ->
               ((let uu____19269 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____19269
                 then
                   let uu____19270 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____19270
                 else ());
                (let uu____19272 =
                   if pop_when_done
                   then
                     FStar_ToSyntax_Env.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____19272, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____19286 = desugar_modul env modul  in
      match uu____19286 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____19313 = desugar_decls env decls  in
      match uu____19313 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____19351 = desugar_partial_modul modul env a_modul  in
        match uu____19351 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____19425 ->
                  let t =
                    let uu____19433 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____19433  in
                  let uu____19442 =
                    let uu____19443 = FStar_Syntax_Subst.compress t  in
                    uu____19443.FStar_Syntax_Syntax.n  in
                  (match uu____19442 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____19453,uu____19454)
                       -> bs1
                   | uu____19475 -> failwith "Impossible")
               in
            let uu____19482 =
              let uu____19489 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____19489
                FStar_Syntax_Syntax.t_unit
               in
            match uu____19482 with
            | (binders,uu____19491,binders_opening) ->
                let erase_term t =
                  let uu____19497 =
                    let uu____19498 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____19498  in
                  FStar_Syntax_Subst.close binders uu____19497  in
                let erase_tscheme uu____19514 =
                  match uu____19514 with
                  | (us,t) ->
                      let t1 =
                        let uu____19534 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____19534 t  in
                      let uu____19537 =
                        let uu____19538 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____19538  in
                      ([], uu____19537)
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
                    | uu____19567 ->
                        let bs =
                          let uu____19575 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____19575  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____19605 =
                          let uu____19606 =
                            let uu____19609 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____19609  in
                          uu____19606.FStar_Syntax_Syntax.n  in
                        (match uu____19605 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____19617,uu____19618) -> bs1
                         | uu____19639 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____19650 =
                      let uu____19651 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____19651  in
                    FStar_Syntax_Subst.close binders uu____19650  in
                  let uu___139_19652 = action  in
                  let uu____19653 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____19654 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___139_19652.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___139_19652.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____19653;
                    FStar_Syntax_Syntax.action_typ = uu____19654
                  }  in
                let uu___140_19655 = ed  in
                let uu____19656 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____19657 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____19658 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____19659 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____19660 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____19661 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____19662 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____19663 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____19664 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____19665 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____19666 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____19667 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____19668 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____19669 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____19670 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____19671 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___140_19655.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___140_19655.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____19656;
                  FStar_Syntax_Syntax.signature = uu____19657;
                  FStar_Syntax_Syntax.ret_wp = uu____19658;
                  FStar_Syntax_Syntax.bind_wp = uu____19659;
                  FStar_Syntax_Syntax.if_then_else = uu____19660;
                  FStar_Syntax_Syntax.ite_wp = uu____19661;
                  FStar_Syntax_Syntax.stronger = uu____19662;
                  FStar_Syntax_Syntax.close_wp = uu____19663;
                  FStar_Syntax_Syntax.assert_p = uu____19664;
                  FStar_Syntax_Syntax.assume_p = uu____19665;
                  FStar_Syntax_Syntax.null_wp = uu____19666;
                  FStar_Syntax_Syntax.trivial = uu____19667;
                  FStar_Syntax_Syntax.repr = uu____19668;
                  FStar_Syntax_Syntax.return_repr = uu____19669;
                  FStar_Syntax_Syntax.bind_repr = uu____19670;
                  FStar_Syntax_Syntax.actions = uu____19671
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___141_19683 = se  in
                  let uu____19684 =
                    let uu____19685 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____19685  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19684;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___141_19683.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___141_19683.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___141_19683.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___141_19683.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___142_19689 = se  in
                  let uu____19690 =
                    let uu____19691 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19691
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19690;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___142_19689.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___142_19689.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___142_19689.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___142_19689.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____19693 -> FStar_ToSyntax_Env.push_sigelt env se  in
          let uu____19694 =
            FStar_ToSyntax_Env.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____19694 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____19706 =
                  FStar_ToSyntax_Env.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____19706
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_ToSyntax_Env.finish en2 m  in
              let uu____19708 =
                if pop_when_done
                then
                  FStar_ToSyntax_Env.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____19708)
  