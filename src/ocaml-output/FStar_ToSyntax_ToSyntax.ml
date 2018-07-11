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
      fun uu___232_74  ->
        match uu___232_74 with
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
  fun uu___233_83  ->
    match uu___233_83 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.PushOptions sopt ->
        FStar_Syntax_Syntax.PushOptions sopt
    | FStar_Parser_AST.PopOptions  -> FStar_Syntax_Syntax.PopOptions
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___234_97  ->
    match uu___234_97 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____100 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____107 .
    FStar_Parser_AST.imp ->
      'Auu____107 ->
        ('Auu____107,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____132 .
    FStar_Parser_AST.imp ->
      'Auu____132 ->
        ('Auu____132,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____151 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____168 -> true
            | uu____173 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____180 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____186 =
      let uu____187 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____187  in
    FStar_Parser_AST.mk_term uu____186 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____193 =
      let uu____194 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____194  in
    FStar_Parser_AST.mk_term uu____193 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____205 =
        let uu____206 = unparen t  in uu____206.FStar_Parser_AST.tm  in
      match uu____205 with
      | FStar_Parser_AST.Name l ->
          let uu____208 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____208 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____214) ->
          let uu____227 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____227 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____233,uu____234) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____237,uu____238) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____243,t1) -> is_comp_type env t1
      | uu____245 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____261 =
          let uu____264 =
            let uu____265 =
              let uu____270 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____270, r)  in
            FStar_Ident.mk_ident uu____265  in
          [uu____264]  in
        FStar_All.pipe_right uu____261 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____283 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____283 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____319 =
              let uu____320 =
                let uu____321 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____321 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____320 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____319  in
          let fallback uu____329 =
            let uu____330 = FStar_Ident.text_of_id op  in
            match uu____330 with
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
                let uu____333 = FStar_Options.ml_ish ()  in
                if uu____333
                then
                  r FStar_Parser_Const.list_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
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
            | uu____337 -> FStar_Pervasives_Native.None  in
          let uu____338 =
            let uu____345 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____345  in
          match uu____338 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____357 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____375 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____375
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____422 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____426 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____426 with | (env1,uu____438) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____441,term) ->
          let uu____443 = free_type_vars env term  in (env, uu____443)
      | FStar_Parser_AST.TAnnotated (id1,uu____449) ->
          let uu____450 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____450 with | (env1,uu____462) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____466 = free_type_vars env t  in (env, uu____466)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____473 =
        let uu____474 = unparen t  in uu____474.FStar_Parser_AST.tm  in
      match uu____473 with
      | FStar_Parser_AST.Labeled uu____477 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____487 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____487 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____500 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____507 -> []
      | FStar_Parser_AST.Uvar uu____508 -> []
      | FStar_Parser_AST.Var uu____509 -> []
      | FStar_Parser_AST.Projector uu____510 -> []
      | FStar_Parser_AST.Discrim uu____515 -> []
      | FStar_Parser_AST.Name uu____516 -> []
      | FStar_Parser_AST.Requires (t1,uu____518) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____524) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____529,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____547,ts) ->
          FStar_List.collect
            (fun uu____568  ->
               match uu____568 with | (t1,uu____576) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____577,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____585) ->
          let uu____586 = free_type_vars env t1  in
          let uu____589 = free_type_vars env t2  in
          FStar_List.append uu____586 uu____589
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____594 = free_type_vars_b env b  in
          (match uu____594 with
           | (env1,f) ->
               let uu____609 = free_type_vars env1 t1  in
               FStar_List.append f uu____609)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____618 =
            FStar_List.fold_left
              (fun uu____638  ->
                 fun binder  ->
                   match uu____638 with
                   | (env1,free) ->
                       let uu____658 = free_type_vars_b env1 binder  in
                       (match uu____658 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____618 with
           | (env1,free) ->
               let uu____689 = free_type_vars env1 body  in
               FStar_List.append free uu____689)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____698 =
            FStar_List.fold_left
              (fun uu____718  ->
                 fun binder  ->
                   match uu____718 with
                   | (env1,free) ->
                       let uu____738 = free_type_vars_b env1 binder  in
                       (match uu____738 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____698 with
           | (env1,free) ->
               let uu____769 = free_type_vars env1 body  in
               FStar_List.append free uu____769)
      | FStar_Parser_AST.Project (t1,uu____773) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____777 -> []
      | FStar_Parser_AST.Let uu____784 -> []
      | FStar_Parser_AST.LetOpen uu____805 -> []
      | FStar_Parser_AST.If uu____810 -> []
      | FStar_Parser_AST.QForall uu____817 -> []
      | FStar_Parser_AST.QExists uu____830 -> []
      | FStar_Parser_AST.Record uu____843 -> []
      | FStar_Parser_AST.Match uu____856 -> []
      | FStar_Parser_AST.TryWith uu____871 -> []
      | FStar_Parser_AST.Bind uu____886 -> []
      | FStar_Parser_AST.Quote uu____893 -> []
      | FStar_Parser_AST.VQuote uu____898 -> []
      | FStar_Parser_AST.Antiquote uu____899 -> []
      | FStar_Parser_AST.Seq uu____900 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____953 =
        let uu____954 = unparen t1  in uu____954.FStar_Parser_AST.tm  in
      match uu____953 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____996 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1020 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1020  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1038 =
                     let uu____1039 =
                       let uu____1044 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1044)  in
                     FStar_Parser_AST.TAnnotated uu____1039  in
                   FStar_Parser_AST.mk_binder uu____1038
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
        let uu____1061 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1061  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1079 =
                     let uu____1080 =
                       let uu____1085 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1085)  in
                     FStar_Parser_AST.TAnnotated uu____1080  in
                   FStar_Parser_AST.mk_binder uu____1079
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1087 =
             let uu____1088 = unparen t  in uu____1088.FStar_Parser_AST.tm
              in
           match uu____1087 with
           | FStar_Parser_AST.Product uu____1089 -> t
           | uu____1096 ->
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
      | uu____1132 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1140,uu____1141) -> true
    | FStar_Parser_AST.PatVar (uu____1146,uu____1147) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1153) -> is_var_pattern p1
    | uu____1166 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1173) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1186;
           FStar_Parser_AST.prange = uu____1187;_},uu____1188)
        -> true
    | uu____1199 -> false
  
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
    | uu____1213 -> p
  
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
            let uu____1283 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1283 with
             | (name,args,uu____1326) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1376);
               FStar_Parser_AST.prange = uu____1377;_},args)
            when is_top_level1 ->
            let uu____1387 =
              let uu____1392 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1392  in
            (uu____1387, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1414);
               FStar_Parser_AST.prange = uu____1415;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1445 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1495 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1496,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1499 -> acc
      | FStar_Parser_AST.PatTvar uu____1500 -> acc
      | FStar_Parser_AST.PatOp uu____1507 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1515) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1524) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1539 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1539
      | FStar_Parser_AST.PatAscribed (pat,uu____1547) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1609 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1645 -> false
  
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
  fun uu___235_1691  ->
    match uu___235_1691 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1698 -> failwith "Impossible"
  
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
  fun uu____1731  ->
    match uu____1731 with
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
      let uu____1811 =
        let uu____1828 =
          let uu____1831 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1831  in
        let uu____1832 =
          let uu____1843 =
            let uu____1852 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1852)  in
          [uu____1843]  in
        (uu____1828, uu____1832)  in
      FStar_Syntax_Syntax.Tm_app uu____1811  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1899 =
        let uu____1916 =
          let uu____1919 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1919  in
        let uu____1920 =
          let uu____1931 =
            let uu____1940 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1940)  in
          [uu____1931]  in
        (uu____1916, uu____1920)  in
      FStar_Syntax_Syntax.Tm_app uu____1899  in
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
          let uu____2001 =
            let uu____2018 =
              let uu____2021 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2021  in
            let uu____2022 =
              let uu____2033 =
                let uu____2042 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2042)  in
              let uu____2049 =
                let uu____2060 =
                  let uu____2069 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2069)  in
                [uu____2060]  in
              uu____2033 :: uu____2049  in
            (uu____2018, uu____2022)  in
          FStar_Syntax_Syntax.Tm_app uu____2001  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2127 =
        let uu____2142 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2161  ->
               match uu____2161 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2172;
                    FStar_Syntax_Syntax.index = uu____2173;
                    FStar_Syntax_Syntax.sort = t;_},uu____2175)
                   ->
                   let uu____2182 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2182) uu____2142
         in
      FStar_All.pipe_right bs uu____2127  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2198 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2215 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2241 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2262,uu____2263,bs,t,uu____2266,uu____2267)
                            ->
                            let uu____2276 = bs_univnames bs  in
                            let uu____2279 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2276 uu____2279
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2282,uu____2283,t,uu____2285,uu____2286,uu____2287)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2292 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2241 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___261_2300 = s  in
        let uu____2301 =
          let uu____2302 =
            let uu____2311 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2329,bs,t,lids1,lids2) ->
                          let uu___262_2342 = se  in
                          let uu____2343 =
                            let uu____2344 =
                              let uu____2361 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2362 =
                                let uu____2363 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2363 t  in
                              (lid, uvs, uu____2361, uu____2362, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2344
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2343;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___262_2342.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___262_2342.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___262_2342.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___262_2342.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2377,t,tlid,n1,lids1) ->
                          let uu___263_2386 = se  in
                          let uu____2387 =
                            let uu____2388 =
                              let uu____2403 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2403, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2388  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2387;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___263_2386.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___263_2386.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___263_2386.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___263_2386.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2406 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2311, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2302  in
        {
          FStar_Syntax_Syntax.sigel = uu____2301;
          FStar_Syntax_Syntax.sigrng =
            (uu___261_2300.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___261_2300.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___261_2300.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___261_2300.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2412,t) ->
        let uvs =
          let uu____2415 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2415 FStar_Util.set_elements  in
        let uu___264_2420 = s  in
        let uu____2421 =
          let uu____2422 =
            let uu____2429 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2429)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2422  in
        {
          FStar_Syntax_Syntax.sigel = uu____2421;
          FStar_Syntax_Syntax.sigrng =
            (uu___264_2420.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___264_2420.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___264_2420.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___264_2420.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2451 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2454 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2461) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2494,(FStar_Util.Inl t,uu____2496),uu____2497)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2544,(FStar_Util.Inr c,uu____2546),uu____2547)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2594 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2595,(FStar_Util.Inl t,uu____2597),uu____2598) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2645,(FStar_Util.Inr c,uu____2647),uu____2648) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2695 -> empty_set  in
          FStar_Util.set_union uu____2451 uu____2454  in
        let all_lb_univs =
          let uu____2699 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2715 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2715) empty_set)
             in
          FStar_All.pipe_right uu____2699 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___265_2725 = s  in
        let uu____2726 =
          let uu____2727 =
            let uu____2734 =
              let uu____2735 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___266_2747 = lb  in
                        let uu____2748 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2751 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___266_2747.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2748;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___266_2747.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2751;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___266_2747.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___266_2747.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2735)  in
            (uu____2734, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2727  in
        {
          FStar_Syntax_Syntax.sigel = uu____2726;
          FStar_Syntax_Syntax.sigrng =
            (uu___265_2725.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___265_2725.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___265_2725.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___265_2725.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2759,fml) ->
        let uvs =
          let uu____2762 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2762 FStar_Util.set_elements  in
        let uu___267_2767 = s  in
        let uu____2768 =
          let uu____2769 =
            let uu____2776 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2776)  in
          FStar_Syntax_Syntax.Sig_assume uu____2769  in
        {
          FStar_Syntax_Syntax.sigel = uu____2768;
          FStar_Syntax_Syntax.sigrng =
            (uu___267_2767.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___267_2767.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___267_2767.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___267_2767.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2778,bs,c,flags1) ->
        let uvs =
          let uu____2787 =
            let uu____2790 = bs_univnames bs  in
            let uu____2793 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2790 uu____2793  in
          FStar_All.pipe_right uu____2787 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___268_2801 = s  in
        let uu____2802 =
          let uu____2803 =
            let uu____2816 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____2817 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2816, uu____2817, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2803  in
        {
          FStar_Syntax_Syntax.sigel = uu____2802;
          FStar_Syntax_Syntax.sigrng =
            (uu___268_2801.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___268_2801.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___268_2801.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___268_2801.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____2820 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___236_2825  ->
    match uu___236_2825 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2826 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2838 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2838)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2857 =
      let uu____2858 = unparen t  in uu____2858.FStar_Parser_AST.tm  in
    match uu____2857 with
    | FStar_Parser_AST.Wild  ->
        let uu____2863 =
          let uu____2864 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2864  in
        FStar_Util.Inr uu____2863
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2875)) ->
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
             let uu____2940 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2940
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2951 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2951
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2962 =
               let uu____2967 =
                 let uu____2968 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2968
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2967)
                in
             FStar_Errors.raise_error uu____2962 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2973 ->
        let rec aux t1 univargs =
          let uu____3007 =
            let uu____3008 = unparen t1  in uu____3008.FStar_Parser_AST.tm
             in
          match uu____3007 with
          | FStar_Parser_AST.App (t2,targ,uu____3015) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___237_3038  ->
                     match uu___237_3038 with
                     | FStar_Util.Inr uu____3043 -> true
                     | uu____3044 -> false) univargs
              then
                let uu____3049 =
                  let uu____3050 =
                    FStar_List.map
                      (fun uu___238_3059  ->
                         match uu___238_3059 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3050  in
                FStar_Util.Inr uu____3049
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___239_3076  ->
                        match uu___239_3076 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3082 -> failwith "impossible")
                     univargs
                    in
                 let uu____3083 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3083)
          | uu____3089 ->
              let uu____3090 =
                let uu____3095 =
                  let uu____3096 =
                    let uu____3097 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3097 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3096  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3095)  in
              FStar_Errors.raise_error uu____3090 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3106 ->
        let uu____3107 =
          let uu____3112 =
            let uu____3113 =
              let uu____3114 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3114 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3113  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3112)  in
        FStar_Errors.raise_error uu____3107 t.FStar_Parser_AST.range
  
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
    | (bv,{
            FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_quoted
              (e,{
                   FStar_Syntax_Syntax.qkind =
                     FStar_Syntax_Syntax.Quote_dynamic ;
                   FStar_Syntax_Syntax.antiquotes = uu____3144;_});
            FStar_Syntax_Syntax.pos = uu____3145;
            FStar_Syntax_Syntax.vars = uu____3146;_})::uu____3147
        ->
        let uu____3178 =
          let uu____3183 =
            let uu____3184 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3184
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3183)  in
        FStar_Errors.raise_error uu____3178 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____3187 ->
        let uu____3206 =
          let uu____3211 =
            let uu____3212 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3212
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3211)  in
        FStar_Errors.raise_error uu____3206 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3221 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3221) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3249 = FStar_List.hd fields  in
        match uu____3249 with
        | (f,uu____3259) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3271 =
                match uu____3271 with
                | (f',uu____3277) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3279 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3279
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
              (let uu____3283 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3283);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____3672 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____3679 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____3680 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____3682,pats1) ->
                let aux out uu____3720 =
                  match uu____3720 with
                  | (p2,uu____3732) ->
                      let intersection =
                        let uu____3740 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3740 out  in
                      let uu____3743 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3743
                      then
                        let uu____3746 = pat_vars p2  in
                        FStar_Util.set_union out uu____3746
                      else
                        (let duplicate_bv =
                           let uu____3751 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3751  in
                         let uu____3754 =
                           let uu____3759 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3759)
                            in
                         FStar_Errors.raise_error uu____3754 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3779 = pat_vars p1  in
              FStar_All.pipe_right uu____3779 (fun a236  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3807 =
                  let uu____3808 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3808  in
                if uu____3807
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3815 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3815  in
                   let first_nonlinear_var =
                     let uu____3819 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3819  in
                   let uu____3822 =
                     let uu____3827 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3827)  in
                   FStar_Errors.raise_error uu____3822 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3831) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3832) -> ()
         | (true ,uu____3839) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3862 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____3862 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3878 ->
               let uu____3881 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____3881 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3993 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____4009 =
                 let uu____4010 =
                   let uu____4011 =
                     let uu____4018 =
                       let uu____4019 =
                         let uu____4024 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____4024, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____4019  in
                     (uu____4018, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____4011  in
                 {
                   FStar_Parser_AST.pat = uu____4010;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____4009
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____4041 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____4042 = aux loc env1 p2  in
                 match uu____4042 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___269_4100 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___270_4105 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___270_4105.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___270_4105.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___269_4100.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___271_4107 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___272_4112 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___272_4112.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___272_4112.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___271_4107.FStar_Syntax_Syntax.p)
                           }
                       | uu____4113 when top -> p4
                       | uu____4114 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____4117 =
                       match binder with
                       | LetBinder uu____4130 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____4150 = close_fun env1 t  in
                             desugar_term env1 uu____4150  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____4152 -> true)
                            then
                              (let uu____4153 =
                                 let uu____4158 =
                                   let uu____4159 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____4160 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____4161 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____4159 uu____4160 uu____4161
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____4158)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____4153)
                            else ();
                            (let uu____4163 = annot_pat_var p3 t1  in
                             (uu____4163,
                               (LocalBinder
                                  ((let uu___273_4169 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___273_4169.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___273_4169.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____4117 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4191 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4191, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4200 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4200, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4217 = resolvex loc env1 x  in
               (match uu____4217 with
                | (loc1,env2,xbv) ->
                    let uu____4239 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4239, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4256 = resolvex loc env1 x  in
               (match uu____4256 with
                | (loc1,env2,xbv) ->
                    let uu____4278 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4278, imp))
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
               let uu____4288 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4288, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____4310;_},args)
               ->
               let uu____4316 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____4357  ->
                        match uu____4357 with
                        | (loc1,env2,args1) ->
                            let uu____4405 = aux loc1 env2 arg  in
                            (match uu____4405 with
                             | (loc2,env3,uu____4434,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____4316 with
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
                    let uu____4504 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____4504, false))
           | FStar_Parser_AST.PatApp uu____4519 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____4541 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____4574  ->
                        match uu____4574 with
                        | (loc1,env2,pats1) ->
                            let uu____4606 = aux loc1 env2 pat  in
                            (match uu____4606 with
                             | (loc2,env3,uu____4631,pat1,uu____4633) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____4541 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____4676 =
                        let uu____4679 =
                          let uu____4686 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____4686  in
                        let uu____4687 =
                          let uu____4688 =
                            let uu____4701 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____4701, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____4688  in
                        FStar_All.pipe_left uu____4679 uu____4687  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____4733 =
                               let uu____4734 =
                                 let uu____4747 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____4747, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____4734  in
                             FStar_All.pipe_left (pos_r r) uu____4733) pats1
                        uu____4676
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
               let uu____4789 =
                 FStar_List.fold_left
                   (fun uu____4829  ->
                      fun p2  ->
                        match uu____4829 with
                        | (loc1,env2,pats) ->
                            let uu____4878 = aux loc1 env2 p2  in
                            (match uu____4878 with
                             | (loc2,env3,uu____4907,pat,uu____4909) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4789 with
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
                    let uu____5004 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____5004 with
                     | (constr,uu____5026) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____5029 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____5031 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____5031, false)))
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
                      (fun uu____5100  ->
                         match uu____5100 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____5130  ->
                         match uu____5130 with
                         | (f,uu____5136) ->
                             let uu____5137 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____5163  ->
                                       match uu____5163 with
                                       | (g,uu____5169) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____5137 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____5174,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____5181 =
                   let uu____5182 =
                     let uu____5189 =
                       let uu____5190 =
                         let uu____5191 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____5191  in
                       FStar_Parser_AST.mk_pattern uu____5190
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____5189, args)  in
                   FStar_Parser_AST.PatApp uu____5182  in
                 FStar_Parser_AST.mk_pattern uu____5181
                   p1.FStar_Parser_AST.prange
                  in
               let uu____5194 = aux loc env1 app  in
               (match uu____5194 with
                | (env2,e,b,p2,uu____5223) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____5251 =
                            let uu____5252 =
                              let uu____5265 =
                                let uu___274_5266 = fv  in
                                let uu____5267 =
                                  let uu____5270 =
                                    let uu____5271 =
                                      let uu____5278 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____5278)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____5271
                                     in
                                  FStar_Pervasives_Native.Some uu____5270  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___274_5266.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___274_5266.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____5267
                                }  in
                              (uu____5265, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____5252  in
                          FStar_All.pipe_left pos uu____5251
                      | uu____5305 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____5359 = aux' true loc env1 p2  in
               (match uu____5359 with
                | (loc1,env2,var,p3,uu____5386) ->
                    let uu____5391 =
                      FStar_List.fold_left
                        (fun uu____5423  ->
                           fun p4  ->
                             match uu____5423 with
                             | (loc2,env3,ps1) ->
                                 let uu____5456 = aux' true loc2 env3 p4  in
                                 (match uu____5456 with
                                  | (loc3,env4,uu____5481,p5,uu____5483) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____5391 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____5534 ->
               let uu____5535 = aux' true loc env1 p1  in
               (match uu____5535 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____5575 = aux_maybe_or env p  in
         match uu____5575 with
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
            let uu____5634 =
              let uu____5635 =
                let uu____5646 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____5646,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____5635  in
            (env, uu____5634, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____5674 =
                  let uu____5675 =
                    let uu____5680 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____5680, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____5675  in
                mklet uu____5674
            | FStar_Parser_AST.PatVar (x,uu____5682) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____5688);
                   FStar_Parser_AST.prange = uu____5689;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____5709 =
                  let uu____5710 =
                    let uu____5721 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____5722 =
                      let uu____5729 = desugar_term env t  in
                      (uu____5729, tacopt1)  in
                    (uu____5721, uu____5722)  in
                  LetBinder uu____5710  in
                (env, uu____5709, [])
            | uu____5740 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5750 = desugar_data_pat env p is_mut  in
             match uu____5750 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5779;
                       FStar_Syntax_Syntax.p = uu____5780;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5781;
                       FStar_Syntax_Syntax.p = uu____5782;_}::[] -> []
                   | uu____5783 -> p1  in
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
  fun uu____5790  ->
    fun env  ->
      fun pat  ->
        let uu____5793 = desugar_data_pat env pat false  in
        match uu____5793 with | (env1,uu____5809,pat1) -> (env1, pat1)

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
      let uu____5828 = desugar_term_aq env e  in
      match uu____5828 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____5845 = desugar_typ_aq env e  in
      match uu____5845 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5855  ->
        fun range  ->
          match uu____5855 with
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
              ((let uu____5865 =
                  let uu____5866 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5866  in
                if uu____5865
                then
                  let uu____5867 =
                    let uu____5872 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5872)  in
                  FStar_Errors.log_issue range uu____5867
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
                  let uu____5877 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____5877 range  in
                let lid1 =
                  let uu____5881 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____5881 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____5891) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5900 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____5900 range  in
                           let private_fv =
                             let uu____5902 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5902 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___275_5903 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___275_5903.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___275_5903.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5904 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5911 =
                        let uu____5916 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5916)
                         in
                      FStar_Errors.raise_error uu____5911 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____5932 =
                  let uu____5939 =
                    let uu____5940 =
                      let uu____5957 =
                        let uu____5968 =
                          let uu____5977 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____5977)  in
                        [uu____5968]  in
                      (lid1, uu____5957)  in
                    FStar_Syntax_Syntax.Tm_app uu____5940  in
                  FStar_Syntax_Syntax.mk uu____5939  in
                uu____5932 FStar_Pervasives_Native.None range))

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
            let uu____6026 =
              let uu____6035 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____6035 l  in
            match uu____6026 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____6090;
                              FStar_Syntax_Syntax.vars = uu____6091;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6118 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6118 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____6128 =
                                 let uu____6129 =
                                   let uu____6132 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____6132  in
                                 uu____6129.FStar_Syntax_Syntax.n  in
                               match uu____6128 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____6154))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____6155 -> msg
                             else msg  in
                           let uu____6157 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6157
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6160 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6160 " is deprecated"  in
                           let uu____6161 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6161
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____6162 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____6167 =
                      let uu____6168 =
                        let uu____6175 = mk_ref_read tm1  in
                        (uu____6175,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____6168  in
                    FStar_All.pipe_left mk1 uu____6167
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____6193 =
          let uu____6194 = unparen t  in uu____6194.FStar_Parser_AST.tm  in
        match uu____6193 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____6195; FStar_Ident.ident = uu____6196;
              FStar_Ident.nsstr = uu____6197; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____6200 ->
            let uu____6201 =
              let uu____6206 =
                let uu____6207 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____6207  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____6206)  in
            FStar_Errors.raise_error uu____6201 t.FStar_Parser_AST.range
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
          let uu___276_6290 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___276_6290.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___276_6290.FStar_Syntax_Syntax.vars)
          }  in
        let uu____6293 =
          let uu____6294 = unparen top  in uu____6294.FStar_Parser_AST.tm  in
        match uu____6293 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____6299 ->
            let uu____6306 = desugar_formula env top  in (uu____6306, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____6313 = desugar_formula env t  in (uu____6313, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____6320 = desugar_formula env t  in (uu____6320, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____6344 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____6344, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____6346 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____6346, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____6354 =
                let uu____6355 =
                  let uu____6362 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____6362, args)  in
                FStar_Parser_AST.Op uu____6355  in
              FStar_Parser_AST.mk_term uu____6354 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____6365 =
              let uu____6366 =
                let uu____6367 =
                  let uu____6374 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____6374, [e])  in
                FStar_Parser_AST.Op uu____6367  in
              FStar_Parser_AST.mk_term uu____6366 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____6365
        | FStar_Parser_AST.Op (op_star,uu____6378::uu____6379::[]) when
            (let uu____6384 = FStar_Ident.text_of_id op_star  in
             uu____6384 = "*") &&
              (let uu____6386 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____6386 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____6401;_},t1::t2::[])
                  ->
                  let uu____6406 = flatten1 t1  in
                  FStar_List.append uu____6406 [t2]
              | uu____6409 -> [t]  in
            let uu____6410 =
              let uu____6435 =
                let uu____6458 =
                  let uu____6461 = unparen top  in flatten1 uu____6461  in
                FStar_All.pipe_right uu____6458
                  (FStar_List.map
                     (fun t  ->
                        let uu____6496 = desugar_typ_aq env t  in
                        match uu____6496 with
                        | (t',aq) ->
                            let uu____6507 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____6507, aq)))
                 in
              FStar_All.pipe_right uu____6435 FStar_List.unzip  in
            (match uu____6410 with
             | (targs,aqs) ->
                 let uu____6616 =
                   let uu____6621 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____6621
                    in
                 (match uu____6616 with
                  | (tup,uu____6639) ->
                      let uu____6640 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____6640, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____6654 =
              let uu____6655 =
                let uu____6658 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____6658  in
              FStar_All.pipe_left setpos uu____6655  in
            (uu____6654, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____6670 =
              let uu____6675 =
                let uu____6676 =
                  let uu____6677 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____6677 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____6676  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____6675)  in
            FStar_Errors.raise_error uu____6670 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____6688 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____6688 with
             | FStar_Pervasives_Native.None  ->
                 let uu____6695 =
                   let uu____6700 =
                     let uu____6701 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____6701
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____6700)
                    in
                 FStar_Errors.raise_error uu____6695
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____6711 =
                     let uu____6736 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____6798 = desugar_term_aq env t  in
                               match uu____6798 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____6736 FStar_List.unzip  in
                   (match uu____6711 with
                    | (args1,aqs) ->
                        let uu____6931 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6931, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6947)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6962 =
              let uu___277_6963 = top  in
              let uu____6964 =
                let uu____6965 =
                  let uu____6972 =
                    let uu___278_6973 = top  in
                    let uu____6974 =
                      let uu____6975 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6975  in
                    {
                      FStar_Parser_AST.tm = uu____6974;
                      FStar_Parser_AST.range =
                        (uu___278_6973.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___278_6973.FStar_Parser_AST.level)
                    }  in
                  (uu____6972, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6965  in
              {
                FStar_Parser_AST.tm = uu____6964;
                FStar_Parser_AST.range =
                  (uu___277_6963.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___277_6963.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6962
        | FStar_Parser_AST.Construct (n1,(a,uu____6978)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6994 =
                let uu___279_6995 = top  in
                let uu____6996 =
                  let uu____6997 =
                    let uu____7004 =
                      let uu___280_7005 = top  in
                      let uu____7006 =
                        let uu____7007 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____7007  in
                      {
                        FStar_Parser_AST.tm = uu____7006;
                        FStar_Parser_AST.range =
                          (uu___280_7005.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___280_7005.FStar_Parser_AST.level)
                      }  in
                    (uu____7004, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____6997  in
                {
                  FStar_Parser_AST.tm = uu____6996;
                  FStar_Parser_AST.range =
                    (uu___279_6995.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___279_6995.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____6994))
        | FStar_Parser_AST.Construct (n1,(a,uu____7010)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____7025 =
              let uu___281_7026 = top  in
              let uu____7027 =
                let uu____7028 =
                  let uu____7035 =
                    let uu___282_7036 = top  in
                    let uu____7037 =
                      let uu____7038 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____7038  in
                    {
                      FStar_Parser_AST.tm = uu____7037;
                      FStar_Parser_AST.range =
                        (uu___282_7036.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___282_7036.FStar_Parser_AST.level)
                    }  in
                  (uu____7035, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____7028  in
              {
                FStar_Parser_AST.tm = uu____7027;
                FStar_Parser_AST.range =
                  (uu___281_7026.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___281_7026.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____7025
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7039; FStar_Ident.ident = uu____7040;
              FStar_Ident.nsstr = uu____7041; FStar_Ident.str = "Type0";_}
            ->
            let uu____7044 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____7044, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7045; FStar_Ident.ident = uu____7046;
              FStar_Ident.nsstr = uu____7047; FStar_Ident.str = "Type";_}
            ->
            let uu____7050 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____7050, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____7051; FStar_Ident.ident = uu____7052;
               FStar_Ident.nsstr = uu____7053; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____7071 =
              let uu____7072 =
                let uu____7073 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____7073  in
              mk1 uu____7072  in
            (uu____7071, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7074; FStar_Ident.ident = uu____7075;
              FStar_Ident.nsstr = uu____7076; FStar_Ident.str = "Effect";_}
            ->
            let uu____7079 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____7079, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7080; FStar_Ident.ident = uu____7081;
              FStar_Ident.nsstr = uu____7082; FStar_Ident.str = "True";_}
            ->
            let uu____7085 =
              let uu____7086 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7086
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7085, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7087; FStar_Ident.ident = uu____7088;
              FStar_Ident.nsstr = uu____7089; FStar_Ident.str = "False";_}
            ->
            let uu____7092 =
              let uu____7093 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7093
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7092, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____7096;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____7098 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____7098 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____7107 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____7107, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____7108 =
                    let uu____7109 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____7109 txt
                     in
                  failwith uu____7108))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7116 = desugar_name mk1 setpos env true l  in
              (uu____7116, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7119 = desugar_name mk1 setpos env true l  in
              (uu____7119, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____7130 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____7130 with
                | FStar_Pervasives_Native.Some uu____7139 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____7144 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____7144 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____7158 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____7175 =
                    let uu____7176 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____7176  in
                  (uu____7175, noaqs)
              | uu____7177 ->
                  let uu____7184 =
                    let uu____7189 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____7189)  in
                  FStar_Errors.raise_error uu____7184
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____7196 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____7196 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7203 =
                    let uu____7208 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____7208)
                     in
                  FStar_Errors.raise_error uu____7203
                    top.FStar_Parser_AST.range
              | uu____7213 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____7217 = desugar_name mk1 setpos env true lid'  in
                  (uu____7217, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7233 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____7233 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____7252 ->
                       let uu____7259 =
                         FStar_Util.take
                           (fun uu____7283  ->
                              match uu____7283 with
                              | (uu____7288,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____7259 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____7333 =
                              let uu____7358 =
                                FStar_List.map
                                  (fun uu____7401  ->
                                     match uu____7401 with
                                     | (t,imp) ->
                                         let uu____7418 =
                                           desugar_term_aq env t  in
                                         (match uu____7418 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____7358
                                FStar_List.unzip
                               in
                            (match uu____7333 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____7559 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____7559, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____7577 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____7577 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____7584 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____7595 =
              FStar_List.fold_left
                (fun uu____7640  ->
                   fun b  ->
                     match uu____7640 with
                     | (env1,tparams,typs) ->
                         let uu____7697 = desugar_binder env1 b  in
                         (match uu____7697 with
                          | (xopt,t1) ->
                              let uu____7726 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____7735 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____7735)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____7726 with
                               | (env2,x) ->
                                   let uu____7755 =
                                     let uu____7758 =
                                       let uu____7761 =
                                         let uu____7762 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7762
                                          in
                                       [uu____7761]  in
                                     FStar_List.append typs uu____7758  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___283_7788 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___283_7788.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___283_7788.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____7755)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____7595 with
             | (env1,uu____7816,targs) ->
                 let uu____7838 =
                   let uu____7843 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7843
                    in
                 (match uu____7838 with
                  | (tup,uu____7853) ->
                      let uu____7854 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7854, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7873 = uncurry binders t  in
            (match uu____7873 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___240_7917 =
                   match uu___240_7917 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7933 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7933
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7957 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7957 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7990 = aux env [] bs  in (uu____7990, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7999 = desugar_binder env b  in
            (match uu____7999 with
             | (FStar_Pervasives_Native.None ,uu____8010) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____8024 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____8024 with
                  | ((x,uu____8040),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____8053 =
                        let uu____8054 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____8054  in
                      (uu____8053, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____8072 =
              FStar_List.fold_left
                (fun uu____8092  ->
                   fun pat  ->
                     match uu____8092 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____8118,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____8128 =
                                let uu____8131 = free_type_vars env1 t  in
                                FStar_List.append uu____8131 ftvs  in
                              (env1, uu____8128)
                          | FStar_Parser_AST.PatAscribed
                              (uu____8136,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____8147 =
                                let uu____8150 = free_type_vars env1 t  in
                                let uu____8153 =
                                  let uu____8156 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____8156 ftvs  in
                                FStar_List.append uu____8150 uu____8153  in
                              (env1, uu____8147)
                          | uu____8161 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____8072 with
             | (uu____8170,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____8182 =
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
                   FStar_List.append uu____8182 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___241_8239 =
                   match uu___241_8239 with
                   | [] ->
                       let uu____8266 = desugar_term_aq env1 body  in
                       (match uu____8266 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____8303 =
                                      let uu____8304 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____8304
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____8303 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____8373 =
                              let uu____8376 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____8376  in
                            (uu____8373, aq))
                   | p::rest ->
                       let uu____8391 = desugar_binding_pat env1 p  in
                       (match uu____8391 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____8427 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____8434 =
                              match b with
                              | LetBinder uu____8475 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____8543) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____8597 =
                                          let uu____8606 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____8606, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____8597
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____8668,uu____8669) ->
                                             let tup2 =
                                               let uu____8671 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8671
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8675 =
                                                 let uu____8682 =
                                                   let uu____8683 =
                                                     let uu____8700 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____8703 =
                                                       let uu____8714 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____8723 =
                                                         let uu____8734 =
                                                           let uu____8743 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____8743
                                                            in
                                                         [uu____8734]  in
                                                       uu____8714 ::
                                                         uu____8723
                                                        in
                                                     (uu____8700, uu____8703)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8683
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8682
                                                  in
                                               uu____8675
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____8794 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____8794
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____8837,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____8839,pats)) ->
                                             let tupn =
                                               let uu____8882 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8882
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8894 =
                                                 let uu____8895 =
                                                   let uu____8912 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____8915 =
                                                     let uu____8926 =
                                                       let uu____8937 =
                                                         let uu____8946 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____8946
                                                          in
                                                       [uu____8937]  in
                                                     FStar_List.append args
                                                       uu____8926
                                                      in
                                                   (uu____8912, uu____8915)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8895
                                                  in
                                               mk1 uu____8894  in
                                             let p2 =
                                               let uu____8994 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____8994
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____9035 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____8434 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____9128,uu____9129,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____9151 =
                let uu____9152 = unparen e  in uu____9152.FStar_Parser_AST.tm
                 in
              match uu____9151 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____9162 ->
                  let uu____9163 = desugar_term_aq env e  in
                  (match uu____9163 with
                   | (head1,aq) ->
                       let uu____9176 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____9176, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____9183 ->
            let rec aux args aqs e =
              let uu____9260 =
                let uu____9261 = unparen e  in uu____9261.FStar_Parser_AST.tm
                 in
              match uu____9260 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____9279 = desugar_term_aq env t  in
                  (match uu____9279 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____9327 ->
                  let uu____9328 = desugar_term_aq env e  in
                  (match uu____9328 with
                   | (head1,aq) ->
                       let uu____9349 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____9349, (join_aqs (aq :: aqs))))
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
            let uu____9409 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____9409
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
            let uu____9461 = desugar_term_aq env t  in
            (match uu____9461 with
             | (tm,s) ->
                 let uu____9472 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____9472, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____9478 =
              let uu____9491 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____9491 then desugar_typ_aq else desugar_term_aq  in
            uu____9478 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____9546 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____9689  ->
                        match uu____9689 with
                        | (attr_opt,(p,def)) ->
                            let uu____9747 = is_app_pattern p  in
                            if uu____9747
                            then
                              let uu____9778 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____9778, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____9860 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____9860, def1)
                               | uu____9905 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____9943);
                                           FStar_Parser_AST.prange =
                                             uu____9944;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____9992 =
                                            let uu____10013 =
                                              let uu____10018 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____10018  in
                                            (uu____10013, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____9992, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____10109) ->
                                        if top_level
                                        then
                                          let uu____10144 =
                                            let uu____10165 =
                                              let uu____10170 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____10170  in
                                            (uu____10165, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____10144, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____10260 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____10291 =
                FStar_List.fold_left
                  (fun uu____10364  ->
                     fun uu____10365  ->
                       match (uu____10364, uu____10365) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____10473,uu____10474),uu____10475))
                           ->
                           let uu____10592 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____10618 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____10618 with
                                  | (env2,xx) ->
                                      let uu____10637 =
                                        let uu____10640 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____10640 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____10637))
                             | FStar_Util.Inr l ->
                                 let uu____10648 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____10648, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____10592 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____10291 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____10796 =
                    match uu____10796 with
                    | (attrs_opt,(uu____10832,args,result_t),def) ->
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
                                let uu____10920 = is_comp_type env1 t  in
                                if uu____10920
                                then
                                  ((let uu____10922 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____10932 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____10932))
                                       in
                                    match uu____10922 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____10935 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____10937 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____10937))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____10935
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
                          | uu____10944 ->
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
                              let uu____10959 =
                                let uu____10960 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____10960
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____10959
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
                  let uu____11037 = desugar_term_aq env' body  in
                  (match uu____11037 with
                   | (body1,aq) ->
                       let uu____11050 =
                         let uu____11053 =
                           let uu____11054 =
                             let uu____11067 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____11067)  in
                           FStar_Syntax_Syntax.Tm_let uu____11054  in
                         FStar_All.pipe_left mk1 uu____11053  in
                       (uu____11050, aq))
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
              let uu____11147 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____11147 with
              | (env1,binder,pat1) ->
                  let uu____11169 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____11195 = desugar_term_aq env1 t2  in
                        (match uu____11195 with
                         | (body1,aq) ->
                             let fv =
                               let uu____11209 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____11209
                                 FStar_Pervasives_Native.None
                                in
                             let uu____11210 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____11210, aq))
                    | LocalBinder (x,uu____11240) ->
                        let uu____11241 = desugar_term_aq env1 t2  in
                        (match uu____11241 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____11255;
                                   FStar_Syntax_Syntax.p = uu____11256;_}::[]
                                   -> body1
                               | uu____11257 ->
                                   let uu____11260 =
                                     let uu____11267 =
                                       let uu____11268 =
                                         let uu____11291 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____11294 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____11291, uu____11294)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11268
                                        in
                                     FStar_Syntax_Syntax.mk uu____11267  in
                                   uu____11260 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____11334 =
                               let uu____11337 =
                                 let uu____11338 =
                                   let uu____11351 =
                                     let uu____11354 =
                                       let uu____11355 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____11355]  in
                                     FStar_Syntax_Subst.close uu____11354
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____11351)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____11338  in
                               FStar_All.pipe_left mk1 uu____11337  in
                             (uu____11334, aq))
                     in
                  (match uu____11169 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____11418 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____11418, aq)
                       else (tm, aq))
               in
            let uu____11430 = FStar_List.hd lbs  in
            (match uu____11430 with
             | (attrs,(head_pat,defn)) ->
                 let uu____11474 = is_rec || (is_app_pattern head_pat)  in
                 if uu____11474
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____11487 =
                let uu____11488 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____11488  in
              mk1 uu____11487  in
            let uu____11489 = desugar_term_aq env t1  in
            (match uu____11489 with
             | (t1',aq1) ->
                 let uu____11500 = desugar_term_aq env t2  in
                 (match uu____11500 with
                  | (t2',aq2) ->
                      let uu____11511 = desugar_term_aq env t3  in
                      (match uu____11511 with
                       | (t3',aq3) ->
                           let uu____11522 =
                             let uu____11523 =
                               let uu____11524 =
                                 let uu____11547 =
                                   let uu____11564 =
                                     let uu____11579 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____11579,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____11592 =
                                     let uu____11609 =
                                       let uu____11624 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____11624,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____11609]  in
                                   uu____11564 :: uu____11592  in
                                 (t1', uu____11547)  in
                               FStar_Syntax_Syntax.Tm_match uu____11524  in
                             mk1 uu____11523  in
                           (uu____11522, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____11815 =
              match uu____11815 with
              | (pat,wopt,b) ->
                  let uu____11837 = desugar_match_pat env pat  in
                  (match uu____11837 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____11868 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____11868
                          in
                       let uu____11873 = desugar_term_aq env1 b  in
                       (match uu____11873 with
                        | (b1,aq) ->
                            let uu____11886 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____11886, aq)))
               in
            let uu____11891 = desugar_term_aq env e  in
            (match uu____11891 with
             | (e1,aq) ->
                 let uu____11902 =
                   let uu____11933 =
                     let uu____11966 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____11966 FStar_List.unzip  in
                   FStar_All.pipe_right uu____11933
                     (fun uu____12184  ->
                        match uu____12184 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____11902 with
                  | (brs,aqs) ->
                      let uu____12403 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____12403, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____12446 = is_comp_type env t  in
              if uu____12446
              then
                let uu____12455 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____12455
              else
                (let uu____12463 = desugar_term env t  in
                 FStar_Util.Inl uu____12463)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____12477 = desugar_term_aq env e  in
            (match uu____12477 with
             | (e1,aq) ->
                 let uu____12488 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____12488, aq))
        | FStar_Parser_AST.Record (uu____12521,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____12562 = FStar_List.hd fields  in
              match uu____12562 with | (f,uu____12574) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____12620  ->
                        match uu____12620 with
                        | (g,uu____12626) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____12632,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____12646 =
                         let uu____12651 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____12651)
                          in
                       FStar_Errors.raise_error uu____12646
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
                  let uu____12659 =
                    let uu____12670 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____12701  ->
                              match uu____12701 with
                              | (f,uu____12711) ->
                                  let uu____12712 =
                                    let uu____12713 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____12713
                                     in
                                  (uu____12712, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____12670)  in
                  FStar_Parser_AST.Construct uu____12659
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____12731 =
                      let uu____12732 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____12732  in
                    FStar_Parser_AST.mk_term uu____12731
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____12734 =
                      let uu____12747 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____12777  ->
                                match uu____12777 with
                                | (f,uu____12787) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____12747)  in
                    FStar_Parser_AST.Record uu____12734  in
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
            let uu____12847 = desugar_term_aq env recterm1  in
            (match uu____12847 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____12863;
                         FStar_Syntax_Syntax.vars = uu____12864;_},args)
                      ->
                      let uu____12890 =
                        let uu____12891 =
                          let uu____12892 =
                            let uu____12909 =
                              let uu____12912 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____12913 =
                                let uu____12916 =
                                  let uu____12917 =
                                    let uu____12924 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____12924)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____12917
                                   in
                                FStar_Pervasives_Native.Some uu____12916  in
                              FStar_Syntax_Syntax.fvar uu____12912
                                FStar_Syntax_Syntax.delta_constant
                                uu____12913
                               in
                            (uu____12909, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____12892  in
                        FStar_All.pipe_left mk1 uu____12891  in
                      (uu____12890, s)
                  | uu____12953 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____12957 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____12957 with
              | (constrname,is_rec) ->
                  let uu____12972 = desugar_term_aq env e  in
                  (match uu____12972 with
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
                       let uu____12990 =
                         let uu____12991 =
                           let uu____12992 =
                             let uu____13009 =
                               let uu____13012 =
                                 let uu____13013 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____13013
                                  in
                               FStar_Syntax_Syntax.fvar uu____13012
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____13014 =
                               let uu____13025 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____13025]  in
                             (uu____13009, uu____13014)  in
                           FStar_Syntax_Syntax.Tm_app uu____12992  in
                         FStar_All.pipe_left mk1 uu____12991  in
                       (uu____12990, s))))
        | FStar_Parser_AST.NamedTyp (uu____13062,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____13071 =
              let uu____13072 = FStar_Syntax_Subst.compress tm  in
              uu____13072.FStar_Syntax_Syntax.n  in
            (match uu____13071 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____13080 =
                   let uu___284_13081 =
                     let uu____13082 =
                       let uu____13083 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____13083  in
                     FStar_Syntax_Util.exp_string uu____13082  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___284_13081.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___284_13081.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____13080, noaqs)
             | uu____13084 ->
                 let uu____13085 =
                   let uu____13090 =
                     let uu____13091 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____13091
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____13090)  in
                 FStar_Errors.raise_error uu____13085
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____13097 = desugar_term_aq env e  in
            (match uu____13097 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____13109 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____13109, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____13114 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____13115 =
              let uu____13116 =
                let uu____13123 = desugar_term env e  in (bv, uu____13123)
                 in
              [uu____13116]  in
            (uu____13114, uu____13115)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____13148 =
              let uu____13149 =
                let uu____13150 =
                  let uu____13157 = desugar_term env e  in (uu____13157, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____13150  in
              FStar_All.pipe_left mk1 uu____13149  in
            (uu____13148, noaqs)
        | uu____13162 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____13163 = desugar_formula env top  in
            (uu____13163, noaqs)
        | uu____13164 ->
            let uu____13165 =
              let uu____13170 =
                let uu____13171 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____13171  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____13170)  in
            FStar_Errors.raise_error uu____13165 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____13177 -> false
    | uu____13186 -> true

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
           (fun uu____13223  ->
              match uu____13223 with
              | (a,imp) ->
                  let uu____13236 = desugar_term env a  in
                  arg_withimp_e imp uu____13236))

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
        let is_requires uu____13268 =
          match uu____13268 with
          | (t1,uu____13274) ->
              let uu____13275 =
                let uu____13276 = unparen t1  in
                uu____13276.FStar_Parser_AST.tm  in
              (match uu____13275 with
               | FStar_Parser_AST.Requires uu____13277 -> true
               | uu____13284 -> false)
           in
        let is_ensures uu____13294 =
          match uu____13294 with
          | (t1,uu____13300) ->
              let uu____13301 =
                let uu____13302 = unparen t1  in
                uu____13302.FStar_Parser_AST.tm  in
              (match uu____13301 with
               | FStar_Parser_AST.Ensures uu____13303 -> true
               | uu____13310 -> false)
           in
        let is_app head1 uu____13325 =
          match uu____13325 with
          | (t1,uu____13331) ->
              let uu____13332 =
                let uu____13333 = unparen t1  in
                uu____13333.FStar_Parser_AST.tm  in
              (match uu____13332 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____13335;
                      FStar_Parser_AST.level = uu____13336;_},uu____13337,uu____13338)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____13339 -> false)
           in
        let is_smt_pat uu____13349 =
          match uu____13349 with
          | (t1,uu____13355) ->
              let uu____13356 =
                let uu____13357 = unparen t1  in
                uu____13357.FStar_Parser_AST.tm  in
              (match uu____13356 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____13360);
                             FStar_Parser_AST.range = uu____13361;
                             FStar_Parser_AST.level = uu____13362;_},uu____13363)::uu____13364::[])
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
                             FStar_Parser_AST.range = uu____13403;
                             FStar_Parser_AST.level = uu____13404;_},uu____13405)::uu____13406::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____13431 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____13463 = head_and_args t1  in
          match uu____13463 with
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
                   let thunk_ens uu____13561 =
                     match uu____13561 with
                     | (e,i) ->
                         let uu____13572 = thunk_ens_ e  in (uu____13572, i)
                      in
                   let fail_lemma uu____13584 =
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
                         let uu____13664 =
                           let uu____13671 =
                             let uu____13678 = thunk_ens ens  in
                             [uu____13678; nil_pat]  in
                           req_true :: uu____13671  in
                         unit_tm :: uu____13664
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____13725 =
                           let uu____13732 =
                             let uu____13739 = thunk_ens ens  in
                             [uu____13739; nil_pat]  in
                           req :: uu____13732  in
                         unit_tm :: uu____13725
                     | ens::smtpat::[] when
                         (((let uu____13788 = is_requires ens  in
                            Prims.op_Negation uu____13788) &&
                             (let uu____13790 = is_smt_pat ens  in
                              Prims.op_Negation uu____13790))
                            &&
                            (let uu____13792 = is_decreases ens  in
                             Prims.op_Negation uu____13792))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____13793 =
                           let uu____13800 =
                             let uu____13807 = thunk_ens ens  in
                             [uu____13807; smtpat]  in
                           req_true :: uu____13800  in
                         unit_tm :: uu____13793
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____13854 =
                           let uu____13861 =
                             let uu____13868 = thunk_ens ens  in
                             [uu____13868; nil_pat; dec]  in
                           req_true :: uu____13861  in
                         unit_tm :: uu____13854
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13928 =
                           let uu____13935 =
                             let uu____13942 = thunk_ens ens  in
                             [uu____13942; smtpat; dec]  in
                           req_true :: uu____13935  in
                         unit_tm :: uu____13928
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____14002 =
                           let uu____14009 =
                             let uu____14016 = thunk_ens ens  in
                             [uu____14016; nil_pat; dec]  in
                           req :: uu____14009  in
                         unit_tm :: uu____14002
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____14076 =
                           let uu____14083 =
                             let uu____14090 = thunk_ens ens  in
                             [uu____14090; smtpat]  in
                           req :: uu____14083  in
                         unit_tm :: uu____14076
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____14155 =
                           let uu____14162 =
                             let uu____14169 = thunk_ens ens  in
                             [uu____14169; dec; smtpat]  in
                           req :: uu____14162  in
                         unit_tm :: uu____14155
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____14231 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____14231, args)
               | FStar_Parser_AST.Name l when
                   (let uu____14259 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____14259
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____14260 =
                     let uu____14267 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14267, [])  in
                   (uu____14260, args)
               | FStar_Parser_AST.Name l when
                   (let uu____14285 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____14285
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____14286 =
                     let uu____14293 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14293, [])  in
                   (uu____14286, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____14309 =
                     let uu____14316 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14316, [])  in
                   (uu____14309, [(t1, FStar_Parser_AST.Nothing)])
               | uu____14339 ->
                   let default_effect =
                     let uu____14341 = FStar_Options.ml_ish ()  in
                     if uu____14341
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____14344 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____14344
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____14346 =
                     let uu____14353 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14353, [])  in
                   (uu____14346, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____14376 = pre_process_comp_typ t  in
        match uu____14376 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____14425 =
                  let uu____14430 =
                    let uu____14431 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____14431
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____14430)  in
                fail1 uu____14425)
             else ();
             (let is_universe uu____14442 =
                match uu____14442 with
                | (uu____14447,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____14449 = FStar_Util.take is_universe args  in
              match uu____14449 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____14508  ->
                         match uu____14508 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____14515 =
                    let uu____14530 = FStar_List.hd args1  in
                    let uu____14539 = FStar_List.tl args1  in
                    (uu____14530, uu____14539)  in
                  (match uu____14515 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____14594 =
                         let is_decrease uu____14632 =
                           match uu____14632 with
                           | (t1,uu____14642) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____14652;
                                       FStar_Syntax_Syntax.vars = uu____14653;_},uu____14654::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____14693 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____14594 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____14809  ->
                                      match uu____14809 with
                                      | (t1,uu____14819) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____14828,(arg,uu____14830)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____14869 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____14886 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____14897 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____14897
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____14901 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____14901
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____14908 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____14908
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____14912 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____14912
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____14916 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____14916
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____14920 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____14920
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____14938 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____14938
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
                                                  let uu____15027 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____15027
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
                                            | uu____15048 -> pat  in
                                          let uu____15049 =
                                            let uu____15060 =
                                              let uu____15071 =
                                                let uu____15080 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____15080, aq)  in
                                              [uu____15071]  in
                                            ens :: uu____15060  in
                                          req :: uu____15049
                                      | uu____15121 -> rest2
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
        | uu____15145 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___285_15166 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___285_15166.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___285_15166.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___286_15208 = b  in
             {
               FStar_Parser_AST.b = (uu___286_15208.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___286_15208.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___286_15208.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____15271 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____15271)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____15284 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____15284 with
             | (env1,a1) ->
                 let a2 =
                   let uu___287_15294 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___287_15294.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___287_15294.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____15320 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____15334 =
                     let uu____15337 =
                       let uu____15338 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____15338]  in
                     no_annot_abs uu____15337 body2  in
                   FStar_All.pipe_left setpos uu____15334  in
                 let uu____15359 =
                   let uu____15360 =
                     let uu____15377 =
                       let uu____15380 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____15380
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____15381 =
                       let uu____15392 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____15392]  in
                     (uu____15377, uu____15381)  in
                   FStar_Syntax_Syntax.Tm_app uu____15360  in
                 FStar_All.pipe_left mk1 uu____15359)
        | uu____15431 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____15511 = q (rest, pats, body)  in
              let uu____15518 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____15511 uu____15518
                FStar_Parser_AST.Formula
               in
            let uu____15519 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____15519 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____15528 -> failwith "impossible"  in
      let uu____15531 =
        let uu____15532 = unparen f  in uu____15532.FStar_Parser_AST.tm  in
      match uu____15531 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____15539,uu____15540) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____15551,uu____15552) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15583 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____15583
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15619 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____15619
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____15662 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____15667 =
        FStar_List.fold_left
          (fun uu____15700  ->
             fun b  ->
               match uu____15700 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___288_15744 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___288_15744.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___288_15744.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___288_15744.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15759 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____15759 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___289_15777 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___289_15777.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___289_15777.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____15778 =
                               let uu____15785 =
                                 let uu____15790 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____15790)  in
                               uu____15785 :: out  in
                             (env2, uu____15778))
                    | uu____15801 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____15667 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____15872 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15872)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____15877 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15877)
      | FStar_Parser_AST.TVariable x ->
          let uu____15881 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____15881)
      | FStar_Parser_AST.NoName t ->
          let uu____15885 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____15885)
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
      fun uu___242_15893  ->
        match uu___242_15893 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____15915 = FStar_Syntax_Syntax.null_binder k  in
            (uu____15915, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____15932 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____15932 with
             | (env1,a1) ->
                 let uu____15949 =
                   let uu____15956 = trans_aqual env1 imp  in
                   ((let uu___290_15962 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___290_15962.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___290_15962.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____15956)
                    in
                 (uu____15949, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___243_15970  ->
      match uu___243_15970 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____15974 =
            let uu____15975 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____15975  in
          FStar_Pervasives_Native.Some uu____15974
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
               (fun uu___244_16011  ->
                  match uu___244_16011 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____16012 -> false))
           in
        let quals2 q =
          let uu____16025 =
            (let uu____16028 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____16028) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____16025
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____16042 = FStar_Ident.range_of_lid disc_name  in
                let uu____16043 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____16042;
                  FStar_Syntax_Syntax.sigquals = uu____16043;
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
            let uu____16082 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____16120  ->
                        match uu____16120 with
                        | (x,uu____16130) ->
                            let uu____16135 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____16135 with
                             | (field_name,uu____16143) ->
                                 let only_decl =
                                   ((let uu____16147 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____16147)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____16149 =
                                        let uu____16150 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____16150.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____16149)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____16166 =
                                       FStar_List.filter
                                         (fun uu___245_16170  ->
                                            match uu___245_16170 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____16171 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____16166
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___246_16184  ->
                                             match uu___246_16184 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____16185 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____16187 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____16187;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____16192 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____16192
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____16197 =
                                        let uu____16202 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____16202  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____16197;
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
                                      let uu____16206 =
                                        let uu____16207 =
                                          let uu____16214 =
                                            let uu____16217 =
                                              let uu____16218 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____16218
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____16217]  in
                                          ((false, [lb]), uu____16214)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____16207
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____16206;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____16082 FStar_List.flatten
  
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
            (lid,uu____16262,t,uu____16264,n1,uu____16266) when
            let uu____16271 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____16271 ->
            let uu____16272 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____16272 with
             | (formals,uu____16290) ->
                 (match formals with
                  | [] -> []
                  | uu____16319 ->
                      let filter_records uu___247_16335 =
                        match uu___247_16335 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____16338,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____16350 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____16352 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____16352 with
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
                      let uu____16362 = FStar_Util.first_N n1 formals  in
                      (match uu____16362 with
                       | (uu____16391,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____16425 -> []
  
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
                    let uu____16503 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____16503
                    then
                      let uu____16506 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____16506
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____16509 =
                      let uu____16514 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____16514  in
                    let uu____16515 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____16520 =
                          let uu____16523 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____16523  in
                        FStar_Syntax_Util.arrow typars uu____16520
                      else FStar_Syntax_Syntax.tun  in
                    let uu____16527 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____16509;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____16515;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____16527;
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
          let tycon_id uu___248_16578 =
            match uu___248_16578 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____16580,uu____16581) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____16591,uu____16592,uu____16593) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____16603,uu____16604,uu____16605) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____16635,uu____16636,uu____16637) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____16681) ->
                let uu____16682 =
                  let uu____16683 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16683  in
                FStar_Parser_AST.mk_term uu____16682 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____16685 =
                  let uu____16686 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16686  in
                FStar_Parser_AST.mk_term uu____16685 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____16688) ->
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
              | uu____16719 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____16727 =
                     let uu____16728 =
                       let uu____16735 = binder_to_term b  in
                       (out, uu____16735, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____16728  in
                   FStar_Parser_AST.mk_term uu____16727
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___249_16747 =
            match uu___249_16747 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____16803  ->
                       match uu____16803 with
                       | (x,t,uu____16814) ->
                           let uu____16819 =
                             let uu____16820 =
                               let uu____16825 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____16825, t)  in
                             FStar_Parser_AST.Annotated uu____16820  in
                           FStar_Parser_AST.mk_binder uu____16819
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____16827 =
                    let uu____16828 =
                      let uu____16829 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____16829  in
                    FStar_Parser_AST.mk_term uu____16828
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____16827 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____16833 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____16860  ->
                          match uu____16860 with
                          | (x,uu____16870,uu____16871) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____16833)
            | uu____16924 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___250_16963 =
            match uu___250_16963 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____16987 = typars_of_binders _env binders  in
                (match uu____16987 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____17023 =
                         let uu____17024 =
                           let uu____17025 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____17025  in
                         FStar_Parser_AST.mk_term uu____17024
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____17023 binders  in
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
            | uu____17036 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____17078 =
              FStar_List.fold_left
                (fun uu____17112  ->
                   fun uu____17113  ->
                     match (uu____17112, uu____17113) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____17182 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____17182 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____17078 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____17273 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____17273
                | uu____17274 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____17282 = desugar_abstract_tc quals env [] tc  in
              (match uu____17282 with
               | (uu____17295,uu____17296,se,uu____17298) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____17301,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____17318 =
                                 let uu____17319 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____17319  in
                               if uu____17318
                               then
                                 let uu____17320 =
                                   let uu____17325 =
                                     let uu____17326 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____17326
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____17325)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____17320
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
                           | uu____17335 ->
                               let uu____17336 =
                                 let uu____17343 =
                                   let uu____17344 =
                                     let uu____17359 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____17359)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____17344
                                    in
                                 FStar_Syntax_Syntax.mk uu____17343  in
                               uu____17336 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___291_17375 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___291_17375.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___291_17375.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___291_17375.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____17376 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____17379 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____17379
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____17392 = typars_of_binders env binders  in
              (match uu____17392 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17426 =
                           FStar_Util.for_some
                             (fun uu___251_17428  ->
                                match uu___251_17428 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____17429 -> false) quals
                            in
                         if uu____17426
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____17434 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____17434
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____17439 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___252_17443  ->
                               match uu___252_17443 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____17444 -> false))
                        in
                     if uu____17439
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____17453 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____17453
                     then
                       let uu____17456 =
                         let uu____17463 =
                           let uu____17464 = unparen t  in
                           uu____17464.FStar_Parser_AST.tm  in
                         match uu____17463 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____17485 =
                               match FStar_List.rev args with
                               | (last_arg,uu____17515)::args_rev ->
                                   let uu____17527 =
                                     let uu____17528 = unparen last_arg  in
                                     uu____17528.FStar_Parser_AST.tm  in
                                   (match uu____17527 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____17556 -> ([], args))
                               | uu____17565 -> ([], args)  in
                             (match uu____17485 with
                              | (cattributes,args1) ->
                                  let uu____17604 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____17604))
                         | uu____17615 -> (t, [])  in
                       match uu____17456 with
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
                                  (fun uu___253_17637  ->
                                     match uu___253_17637 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____17638 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____17645)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____17669 = tycon_record_as_variant trec  in
              (match uu____17669 with
               | (t,fs) ->
                   let uu____17686 =
                     let uu____17689 =
                       let uu____17690 =
                         let uu____17699 =
                           let uu____17702 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____17702  in
                         (uu____17699, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____17690  in
                     uu____17689 :: quals  in
                   desugar_tycon env d uu____17686 [t])
          | uu____17707::uu____17708 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____17875 = et  in
                match uu____17875 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____18100 ->
                         let trec = tc  in
                         let uu____18124 = tycon_record_as_variant trec  in
                         (match uu____18124 with
                          | (t,fs) ->
                              let uu____18183 =
                                let uu____18186 =
                                  let uu____18187 =
                                    let uu____18196 =
                                      let uu____18199 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____18199  in
                                    (uu____18196, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____18187
                                   in
                                uu____18186 :: quals1  in
                              collect_tcs uu____18183 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____18286 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____18286 with
                          | (env2,uu____18346,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____18495 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____18495 with
                          | (env2,uu____18555,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____18680 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____18727 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____18727 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___255_19232  ->
                             match uu___255_19232 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____19297,uu____19298);
                                    FStar_Syntax_Syntax.sigrng = uu____19299;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____19300;
                                    FStar_Syntax_Syntax.sigmeta = uu____19301;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____19302;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____19365 =
                                     typars_of_binders env1 binders  in
                                   match uu____19365 with
                                   | (env2,tpars1) ->
                                       let uu____19392 =
                                         push_tparams env2 tpars1  in
                                       (match uu____19392 with
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
                                 let uu____19421 =
                                   let uu____19440 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____19440)
                                    in
                                 [uu____19421]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____19500);
                                    FStar_Syntax_Syntax.sigrng = uu____19501;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____19503;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____19504;_},constrs,tconstr,quals1)
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
                                 let uu____19602 = push_tparams env1 tpars
                                    in
                                 (match uu____19602 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____19669  ->
                                             match uu____19669 with
                                             | (x,uu____19681) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____19685 =
                                        let uu____19712 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____19820  ->
                                                  match uu____19820 with
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
                                                        let uu____19874 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____19874
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
                                                                uu___254_19885
                                                                 ->
                                                                match uu___254_19885
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____19897
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____19905 =
                                                        let uu____19924 =
                                                          let uu____19925 =
                                                            let uu____19926 =
                                                              let uu____19941
                                                                =
                                                                let uu____19942
                                                                  =
                                                                  let uu____19945
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____19945
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____19942
                                                                 in
                                                              (name, univs1,
                                                                uu____19941,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____19926
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____19925;
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
                                                          uu____19924)
                                                         in
                                                      (name, uu____19905)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____19712
                                         in
                                      (match uu____19685 with
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
                             | uu____20160 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____20286  ->
                             match uu____20286 with
                             | (name_doc,uu____20312,uu____20313) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____20385  ->
                             match uu____20385 with
                             | (uu____20404,uu____20405,se) -> se))
                      in
                   let uu____20431 =
                     let uu____20438 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____20438 rng
                      in
                   (match uu____20431 with
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
                               (fun uu____20500  ->
                                  match uu____20500 with
                                  | (uu____20521,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____20568,tps,k,uu____20571,constrs)
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
                                  | uu____20590 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____20607  ->
                                 match uu____20607 with
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
      let uu____20650 =
        FStar_List.fold_left
          (fun uu____20685  ->
             fun b  ->
               match uu____20685 with
               | (env1,binders1) ->
                   let uu____20729 = desugar_binder env1 b  in
                   (match uu____20729 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____20752 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____20752 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____20805 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____20650 with
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
          let uu____20906 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___256_20911  ->
                    match uu___256_20911 with
                    | FStar_Syntax_Syntax.Reflectable uu____20912 -> true
                    | uu____20913 -> false))
             in
          if uu____20906
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____20916 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____20916
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
      let uu____20948 = FStar_Syntax_Util.head_and_args at1  in
      match uu____20948 with
      | (hd1,args) ->
          let uu____20999 =
            let uu____21014 =
              let uu____21015 = FStar_Syntax_Subst.compress hd1  in
              uu____21015.FStar_Syntax_Syntax.n  in
            (uu____21014, args)  in
          (match uu____20999 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____21038)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____21073 =
                 let uu____21078 =
                   FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_int
                    in
                 FStar_Syntax_Embeddings.unembed uu____21078 a1  in
               (match uu____21073 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____21099 =
                      let uu____21106 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____21106, b)  in
                    FStar_Pervasives_Native.Some uu____21099
                | uu____21117 ->
                    (if warn
                     then
                       FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnappliedFail,
                           "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals")
                     else ();
                     FStar_Pervasives_Native.None))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let b =
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.fail_lax_attr
                  in
               FStar_Pervasives_Native.Some ([], b)
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____21159) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               (if warn
                then
                  FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                    (FStar_Errors.Warning_UnappliedFail,
                      "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals")
                else ();
                FStar_Pervasives_Native.None)
           | uu____21188 -> FStar_Pervasives_Native.None)
  
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
                  let uu____21357 = desugar_binders monad_env eff_binders  in
                  match uu____21357 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____21396 =
                          let uu____21397 =
                            let uu____21406 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____21406  in
                          FStar_List.length uu____21397  in
                        uu____21396 = (Prims.parse_int "1")  in
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
                            (uu____21452,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____21454,uu____21455,uu____21456),uu____21457)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____21490 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____21491 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____21503 = name_of_eff_decl decl  in
                             FStar_List.mem uu____21503 mandatory_members)
                          eff_decls
                         in
                      (match uu____21491 with
                       | (mandatory_members_decls,actions) ->
                           let uu____21520 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____21549  ->
                                     fun decl  ->
                                       match uu____21549 with
                                       | (env2,out) ->
                                           let uu____21569 =
                                             desugar_decl env2 decl  in
                                           (match uu____21569 with
                                            | (env3,ses) ->
                                                let uu____21582 =
                                                  let uu____21585 =
                                                    FStar_List.hd ses  in
                                                  uu____21585 :: out  in
                                                (env3, uu____21582)))
                                  (env1, []))
                              in
                           (match uu____21520 with
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
                                              (uu____21653,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21656,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____21657,
                                                                  (def,uu____21659)::
                                                                  (cps_type,uu____21661)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____21662;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____21663;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____21715 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21715 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21753 =
                                                     let uu____21754 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21755 =
                                                       let uu____21756 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21756
                                                        in
                                                     let uu____21763 =
                                                       let uu____21764 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21764
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21754;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21755;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____21763
                                                     }  in
                                                   (uu____21753, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____21773,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21776,defn),doc1)::[])
                                              when for_free ->
                                              let uu____21811 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21811 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21849 =
                                                     let uu____21850 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21851 =
                                                       let uu____21852 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21852
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21850;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21851;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____21849, doc1))
                                          | uu____21861 ->
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
                                    let uu____21893 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____21893
                                     in
                                  let uu____21894 =
                                    let uu____21895 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____21895
                                     in
                                  ([], uu____21894)  in
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
                                      let uu____21912 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____21912)  in
                                    let uu____21919 =
                                      let uu____21920 =
                                        let uu____21921 =
                                          let uu____21922 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21922
                                           in
                                        let uu____21931 = lookup1 "return"
                                           in
                                        let uu____21932 = lookup1 "bind"  in
                                        let uu____21933 =
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
                                            uu____21921;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____21931;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____21932;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____21933
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____21920
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____21919;
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
                                         (fun uu___257_21939  ->
                                            match uu___257_21939 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____21940 -> true
                                            | uu____21941 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____21955 =
                                       let uu____21956 =
                                         let uu____21957 =
                                           lookup1 "return_wp"  in
                                         let uu____21958 = lookup1 "bind_wp"
                                            in
                                         let uu____21959 =
                                           lookup1 "if_then_else"  in
                                         let uu____21960 = lookup1 "ite_wp"
                                            in
                                         let uu____21961 = lookup1 "stronger"
                                            in
                                         let uu____21962 = lookup1 "close_wp"
                                            in
                                         let uu____21963 = lookup1 "assert_p"
                                            in
                                         let uu____21964 = lookup1 "assume_p"
                                            in
                                         let uu____21965 = lookup1 "null_wp"
                                            in
                                         let uu____21966 = lookup1 "trivial"
                                            in
                                         let uu____21967 =
                                           if rr
                                           then
                                             let uu____21968 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____21968
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____21984 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____21986 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____21988 =
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
                                             uu____21957;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____21958;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____21959;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____21960;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____21961;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____21962;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____21963;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____21964;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____21965;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____21966;
                                           FStar_Syntax_Syntax.repr =
                                             uu____21967;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____21984;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____21986;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____21988
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____21956
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____21955;
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
                                          fun uu____22014  ->
                                            match uu____22014 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____22028 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____22028
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
                let uu____22052 = desugar_binders env1 eff_binders  in
                match uu____22052 with
                | (env2,binders) ->
                    let uu____22089 =
                      let uu____22100 = head_and_args defn  in
                      match uu____22100 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____22137 ->
                                let uu____22138 =
                                  let uu____22143 =
                                    let uu____22144 =
                                      let uu____22145 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____22145 " not found"
                                       in
                                    Prims.strcat "Effect " uu____22144  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____22143)
                                   in
                                FStar_Errors.raise_error uu____22138
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____22147 =
                            match FStar_List.rev args with
                            | (last_arg,uu____22177)::args_rev ->
                                let uu____22189 =
                                  let uu____22190 = unparen last_arg  in
                                  uu____22190.FStar_Parser_AST.tm  in
                                (match uu____22189 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____22218 -> ([], args))
                            | uu____22227 -> ([], args)  in
                          (match uu____22147 with
                           | (cattributes,args1) ->
                               let uu____22270 = desugar_args env2 args1  in
                               let uu____22271 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____22270, uu____22271))
                       in
                    (match uu____22089 with
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
                          (let uu____22307 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____22307 with
                           | (ed_binders,uu____22321,ed_binders_opening) ->
                               let sub1 uu____22334 =
                                 match uu____22334 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____22348 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____22348 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____22352 =
                                       let uu____22353 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____22353)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____22352
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____22362 =
                                   let uu____22363 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____22363
                                    in
                                 let uu____22378 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____22379 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____22380 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____22381 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____22382 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____22383 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____22384 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____22385 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____22386 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____22387 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____22388 =
                                   let uu____22389 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____22389
                                    in
                                 let uu____22404 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____22405 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____22406 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____22414 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____22415 =
                                          let uu____22416 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22416
                                           in
                                        let uu____22431 =
                                          let uu____22432 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22432
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____22414;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____22415;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____22431
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
                                     uu____22362;
                                   FStar_Syntax_Syntax.ret_wp = uu____22378;
                                   FStar_Syntax_Syntax.bind_wp = uu____22379;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____22380;
                                   FStar_Syntax_Syntax.ite_wp = uu____22381;
                                   FStar_Syntax_Syntax.stronger = uu____22382;
                                   FStar_Syntax_Syntax.close_wp = uu____22383;
                                   FStar_Syntax_Syntax.assert_p = uu____22384;
                                   FStar_Syntax_Syntax.assume_p = uu____22385;
                                   FStar_Syntax_Syntax.null_wp = uu____22386;
                                   FStar_Syntax_Syntax.trivial = uu____22387;
                                   FStar_Syntax_Syntax.repr = uu____22388;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____22404;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____22405;
                                   FStar_Syntax_Syntax.actions = uu____22406;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____22449 =
                                     let uu____22450 =
                                       let uu____22459 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____22459
                                        in
                                     FStar_List.length uu____22450  in
                                   uu____22449 = (Prims.parse_int "1")  in
                                 let uu____22490 =
                                   let uu____22493 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____22493 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____22490;
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
                                             let uu____22515 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____22515
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____22517 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____22517
                                 then
                                   let reflect_lid =
                                     let uu____22521 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____22521
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
    let uu____22531 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____22531 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____22582 ->
              let uu____22583 =
                let uu____22584 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____22584
                 in
              Prims.strcat "\n  " uu____22583
          | uu____22585 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____22598  ->
               match uu____22598 with
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
          let uu____22616 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____22616
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____22618 =
          let uu____22629 = FStar_Syntax_Syntax.as_arg arg  in [uu____22629]
           in
        FStar_Syntax_Util.mk_app fv uu____22618

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22660 = desugar_decl_noattrs env d  in
      match uu____22660 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____22678 = mk_comment_attr d  in uu____22678 :: attrs1  in
          let uu____22679 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___292_22685 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___292_22685.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___292_22685.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___292_22685.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___292_22685.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___293_22687 = sigelt  in
                      let uu____22688 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____22694 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____22694) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___293_22687.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___293_22687.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___293_22687.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___293_22687.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____22688
                      })) sigelts
             in
          (env1, uu____22679)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22715 = desugar_decl_aux env d  in
      match uu____22715 with
      | (env1,ses) ->
          let uu____22726 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____22726)

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
      | FStar_Parser_AST.Fsdoc uu____22754 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____22762 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____22762, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____22799  ->
                 match uu____22799 with | (x,uu____22807) -> x) tcs
             in
          let uu____22812 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____22812 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____22834;
                    FStar_Parser_AST.prange = uu____22835;_},uu____22836)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____22845;
                    FStar_Parser_AST.prange = uu____22846;_},uu____22847)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____22862;
                         FStar_Parser_AST.prange = uu____22863;_},uu____22864);
                    FStar_Parser_AST.prange = uu____22865;_},uu____22866)::[]
                   -> false
               | (p,uu____22894)::[] ->
                   let uu____22903 = is_app_pattern p  in
                   Prims.op_Negation uu____22903
               | uu____22904 -> false)
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
            let uu____22977 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____22977 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____22989 =
                     let uu____22990 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____22990.FStar_Syntax_Syntax.n  in
                   match uu____22989 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____23000) ->
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
                         | uu____23033::uu____23034 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____23037 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___258_23052  ->
                                     match uu___258_23052 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____23055;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____23056;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____23057;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____23058;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____23059;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____23060;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____23061;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____23073;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____23074;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____23075;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____23076;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____23077;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____23078;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____23092 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____23123  ->
                                   match uu____23123 with
                                   | (uu____23136,(uu____23137,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____23092
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____23155 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____23155
                         then
                           let uu____23158 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___294_23172 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___295_23174 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___295_23174.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___295_23174.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___294_23172.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___294_23172.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___294_23172.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___294_23172.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___294_23172.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___294_23172.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____23158)
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
                   | uu____23201 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____23207 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____23226 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____23207 with
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
                       let uu___296_23262 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___296_23262.FStar_Parser_AST.prange)
                       }
                   | uu____23269 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___297_23276 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___297_23276.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___297_23276.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___297_23276.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____23312 id1 =
                   match uu____23312 with
                   | (env1,ses) ->
                       let main =
                         let uu____23333 =
                           let uu____23334 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____23334  in
                         FStar_Parser_AST.mk_term uu____23333
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
                       let uu____23384 = desugar_decl env1 id_decl  in
                       (match uu____23384 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____23402 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____23402 FStar_Util.set_elements
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
            let uu____23425 = close_fun env t  in
            desugar_term env uu____23425  in
          let quals1 =
            let uu____23429 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____23429
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____23435 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____23435;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____23443 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____23443 with
           | (t,uu____23457) ->
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
            let uu____23487 =
              let uu____23496 = FStar_Syntax_Syntax.null_binder t  in
              [uu____23496]  in
            let uu____23515 =
              let uu____23518 =
                let uu____23519 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____23519  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____23518
               in
            FStar_Syntax_Util.arrow uu____23487 uu____23515  in
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
            let uu____23580 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____23580 with
            | FStar_Pervasives_Native.None  ->
                let uu____23583 =
                  let uu____23588 =
                    let uu____23589 =
                      let uu____23590 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____23590 " not found"  in
                    Prims.strcat "Effect name " uu____23589  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____23588)  in
                FStar_Errors.raise_error uu____23583
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____23594 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____23612 =
                  let uu____23615 =
                    let uu____23616 = desugar_term env t  in
                    ([], uu____23616)  in
                  FStar_Pervasives_Native.Some uu____23615  in
                (uu____23612, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____23629 =
                  let uu____23632 =
                    let uu____23633 = desugar_term env wp  in
                    ([], uu____23633)  in
                  FStar_Pervasives_Native.Some uu____23632  in
                let uu____23640 =
                  let uu____23643 =
                    let uu____23644 = desugar_term env t  in
                    ([], uu____23644)  in
                  FStar_Pervasives_Native.Some uu____23643  in
                (uu____23629, uu____23640)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____23656 =
                  let uu____23659 =
                    let uu____23660 = desugar_term env t  in
                    ([], uu____23660)  in
                  FStar_Pervasives_Native.Some uu____23659  in
                (FStar_Pervasives_Native.None, uu____23656)
             in
          (match uu____23594 with
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
            let uu____23694 =
              let uu____23695 =
                let uu____23702 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____23702, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____23695  in
            {
              FStar_Syntax_Syntax.sigel = uu____23694;
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
      let uu____23728 =
        FStar_List.fold_left
          (fun uu____23748  ->
             fun d  ->
               match uu____23748 with
               | (env1,sigelts) ->
                   let uu____23768 = desugar_decl env1 d  in
                   (match uu____23768 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____23728 with
      | (env1,sigelts) ->
          let rec forward acc uu___260_23813 =
            match uu___260_23813 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____23827,FStar_Syntax_Syntax.Sig_let uu____23828) ->
                     let uu____23841 =
                       let uu____23844 =
                         let uu___298_23845 = se2  in
                         let uu____23846 =
                           let uu____23849 =
                             FStar_List.filter
                               (fun uu___259_23863  ->
                                  match uu___259_23863 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____23867;
                                           FStar_Syntax_Syntax.vars =
                                             uu____23868;_},uu____23869);
                                      FStar_Syntax_Syntax.pos = uu____23870;
                                      FStar_Syntax_Syntax.vars = uu____23871;_}
                                      when
                                      let uu____23898 =
                                        let uu____23899 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____23899
                                         in
                                      uu____23898 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____23900 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____23849
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___298_23845.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___298_23845.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___298_23845.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___298_23845.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____23846
                         }  in
                       uu____23844 :: se1 :: acc  in
                     forward uu____23841 sigelts1
                 | uu____23905 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____23913 = forward [] sigelts  in (env1, uu____23913)
  
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
          | (FStar_Pervasives_Native.None ,uu____23974) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____23978;
               FStar_Syntax_Syntax.exports = uu____23979;
               FStar_Syntax_Syntax.is_interface = uu____23980;_},FStar_Parser_AST.Module
             (current_lid,uu____23982)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____23990) ->
              let uu____23993 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____23993
           in
        let uu____23998 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____24034 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____24034, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____24051 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____24051, mname, decls, false)
           in
        match uu____23998 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____24081 = desugar_decls env2 decls  in
            (match uu____24081 with
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
          let uu____24143 =
            (FStar_Options.interactive ()) &&
              (let uu____24145 =
                 let uu____24146 =
                   let uu____24147 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____24147  in
                 FStar_Util.get_file_extension uu____24146  in
               FStar_List.mem uu____24145 ["fsti"; "fsi"])
             in
          if uu____24143 then as_interface m else m  in
        let uu____24151 = desugar_modul_common curmod env m1  in
        match uu____24151 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____24169 = FStar_Syntax_DsEnv.pop ()  in
              (uu____24169, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____24189 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____24189 with
      | (env1,modul,pop_when_done) ->
          let uu____24203 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____24203 with
           | (env2,modul1) ->
               ((let uu____24215 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____24215
                 then
                   let uu____24216 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____24216
                 else ());
                (let uu____24218 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____24218, modul1))))
  
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
        (fun uu____24265  ->
           let uu____24266 = desugar_modul env modul  in
           match uu____24266 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____24307  ->
           let uu____24308 = desugar_decls env decls  in
           match uu____24308 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____24362  ->
             let uu____24363 = desugar_partial_modul modul env a_modul  in
             match uu____24363 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____24461 ->
                  let t =
                    let uu____24471 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____24471  in
                  let uu____24484 =
                    let uu____24485 = FStar_Syntax_Subst.compress t  in
                    uu____24485.FStar_Syntax_Syntax.n  in
                  (match uu____24484 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____24497,uu____24498)
                       -> bs1
                   | uu____24523 -> failwith "Impossible")
               in
            let uu____24532 =
              let uu____24539 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____24539
                FStar_Syntax_Syntax.t_unit
               in
            match uu____24532 with
            | (binders,uu____24541,binders_opening) ->
                let erase_term t =
                  let uu____24549 =
                    let uu____24550 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____24550  in
                  FStar_Syntax_Subst.close binders uu____24549  in
                let erase_tscheme uu____24568 =
                  match uu____24568 with
                  | (us,t) ->
                      let t1 =
                        let uu____24588 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____24588 t  in
                      let uu____24591 =
                        let uu____24592 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____24592  in
                      ([], uu____24591)
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
                    | uu____24615 ->
                        let bs =
                          let uu____24625 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____24625  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____24665 =
                          let uu____24666 =
                            let uu____24669 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____24669  in
                          uu____24666.FStar_Syntax_Syntax.n  in
                        (match uu____24665 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____24671,uu____24672) -> bs1
                         | uu____24697 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____24704 =
                      let uu____24705 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____24705  in
                    FStar_Syntax_Subst.close binders uu____24704  in
                  let uu___299_24706 = action  in
                  let uu____24707 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____24708 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___299_24706.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___299_24706.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____24707;
                    FStar_Syntax_Syntax.action_typ = uu____24708
                  }  in
                let uu___300_24709 = ed  in
                let uu____24710 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____24711 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____24712 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____24713 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____24714 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____24715 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____24716 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____24717 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____24718 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____24719 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____24720 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____24721 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____24722 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____24723 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____24724 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____24725 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___300_24709.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___300_24709.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____24710;
                  FStar_Syntax_Syntax.signature = uu____24711;
                  FStar_Syntax_Syntax.ret_wp = uu____24712;
                  FStar_Syntax_Syntax.bind_wp = uu____24713;
                  FStar_Syntax_Syntax.if_then_else = uu____24714;
                  FStar_Syntax_Syntax.ite_wp = uu____24715;
                  FStar_Syntax_Syntax.stronger = uu____24716;
                  FStar_Syntax_Syntax.close_wp = uu____24717;
                  FStar_Syntax_Syntax.assert_p = uu____24718;
                  FStar_Syntax_Syntax.assume_p = uu____24719;
                  FStar_Syntax_Syntax.null_wp = uu____24720;
                  FStar_Syntax_Syntax.trivial = uu____24721;
                  FStar_Syntax_Syntax.repr = uu____24722;
                  FStar_Syntax_Syntax.return_repr = uu____24723;
                  FStar_Syntax_Syntax.bind_repr = uu____24724;
                  FStar_Syntax_Syntax.actions = uu____24725;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___300_24709.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___301_24741 = se  in
                  let uu____24742 =
                    let uu____24743 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____24743  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24742;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___301_24741.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___301_24741.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___301_24741.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___301_24741.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___302_24747 = se  in
                  let uu____24748 =
                    let uu____24749 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24749
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24748;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___302_24747.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___302_24747.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___302_24747.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___302_24747.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____24751 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____24752 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____24752 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____24764 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____24764
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____24766 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____24766)
  