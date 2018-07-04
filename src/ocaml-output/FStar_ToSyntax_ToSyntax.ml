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
      | FStar_Parser_AST.Seq uu____904 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____957 =
        let uu____958 = unparen t1  in uu____958.FStar_Parser_AST.tm  in
      match uu____957 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1000 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1024 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1024  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1042 =
                     let uu____1043 =
                       let uu____1048 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1048)  in
                     FStar_Parser_AST.TAnnotated uu____1043  in
                   FStar_Parser_AST.mk_binder uu____1042
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
        let uu____1065 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1065  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1083 =
                     let uu____1084 =
                       let uu____1089 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1089)  in
                     FStar_Parser_AST.TAnnotated uu____1084  in
                   FStar_Parser_AST.mk_binder uu____1083
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1091 =
             let uu____1092 = unparen t  in uu____1092.FStar_Parser_AST.tm
              in
           match uu____1091 with
           | FStar_Parser_AST.Product uu____1093 -> t
           | uu____1100 ->
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
      | uu____1136 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1144,uu____1145) -> true
    | FStar_Parser_AST.PatVar (uu____1150,uu____1151) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1157) -> is_var_pattern p1
    | uu____1170 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1177) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1190;
           FStar_Parser_AST.prange = uu____1191;_},uu____1192)
        -> true
    | uu____1203 -> false
  
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
    | uu____1217 -> p
  
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
            let uu____1287 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1287 with
             | (name,args,uu____1330) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1380);
               FStar_Parser_AST.prange = uu____1381;_},args)
            when is_top_level1 ->
            let uu____1391 =
              let uu____1396 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1396  in
            (uu____1391, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1418);
               FStar_Parser_AST.prange = uu____1419;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1449 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1499 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1500,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1503 -> acc
      | FStar_Parser_AST.PatTvar uu____1504 -> acc
      | FStar_Parser_AST.PatOp uu____1511 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1519) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1528) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1543 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1543
      | FStar_Parser_AST.PatAscribed (pat,uu____1551) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1613 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1649 -> false
  
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
  fun uu___235_1695  ->
    match uu___235_1695 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1702 -> failwith "Impossible"
  
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
  fun uu____1735  ->
    match uu____1735 with
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
      let uu____1815 =
        let uu____1832 =
          let uu____1835 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1835  in
        let uu____1836 =
          let uu____1847 =
            let uu____1856 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1856)  in
          [uu____1847]  in
        (uu____1832, uu____1836)  in
      FStar_Syntax_Syntax.Tm_app uu____1815  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1903 =
        let uu____1920 =
          let uu____1923 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1923  in
        let uu____1924 =
          let uu____1935 =
            let uu____1944 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1944)  in
          [uu____1935]  in
        (uu____1920, uu____1924)  in
      FStar_Syntax_Syntax.Tm_app uu____1903  in
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
          let uu____2005 =
            let uu____2022 =
              let uu____2025 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2025  in
            let uu____2026 =
              let uu____2037 =
                let uu____2046 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2046)  in
              let uu____2053 =
                let uu____2064 =
                  let uu____2073 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2073)  in
                [uu____2064]  in
              uu____2037 :: uu____2053  in
            (uu____2022, uu____2026)  in
          FStar_Syntax_Syntax.Tm_app uu____2005  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2131 =
        let uu____2146 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2165  ->
               match uu____2165 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2176;
                    FStar_Syntax_Syntax.index = uu____2177;
                    FStar_Syntax_Syntax.sort = t;_},uu____2179)
                   ->
                   let uu____2186 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2186) uu____2146
         in
      FStar_All.pipe_right bs uu____2131  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2202 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2219 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2245 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2266,uu____2267,bs,t,uu____2270,uu____2271)
                            ->
                            let uu____2280 = bs_univnames bs  in
                            let uu____2283 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2280 uu____2283
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2286,uu____2287,t,uu____2289,uu____2290,uu____2291)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2296 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2245 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___261_2304 = s  in
        let uu____2305 =
          let uu____2306 =
            let uu____2315 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2333,bs,t,lids1,lids2) ->
                          let uu___262_2346 = se  in
                          let uu____2347 =
                            let uu____2348 =
                              let uu____2365 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2366 =
                                let uu____2367 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2367 t  in
                              (lid, uvs, uu____2365, uu____2366, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2348
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2347;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___262_2346.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___262_2346.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___262_2346.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___262_2346.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2381,t,tlid,n1,lids1) ->
                          let uu___263_2390 = se  in
                          let uu____2391 =
                            let uu____2392 =
                              let uu____2407 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2407, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2392  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2391;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___263_2390.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___263_2390.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___263_2390.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___263_2390.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2410 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2315, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2306  in
        {
          FStar_Syntax_Syntax.sigel = uu____2305;
          FStar_Syntax_Syntax.sigrng =
            (uu___261_2304.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___261_2304.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___261_2304.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___261_2304.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2416,t) ->
        let uvs =
          let uu____2419 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2419 FStar_Util.set_elements  in
        let uu___264_2424 = s  in
        let uu____2425 =
          let uu____2426 =
            let uu____2433 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2433)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2426  in
        {
          FStar_Syntax_Syntax.sigel = uu____2425;
          FStar_Syntax_Syntax.sigrng =
            (uu___264_2424.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___264_2424.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___264_2424.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___264_2424.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2455 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2458 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2465) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2498,(FStar_Util.Inl t,uu____2500),uu____2501)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2548,(FStar_Util.Inr c,uu____2550),uu____2551)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2598 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2599,(FStar_Util.Inl t,uu____2601),uu____2602) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2649,(FStar_Util.Inr c,uu____2651),uu____2652) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2699 -> empty_set  in
          FStar_Util.set_union uu____2455 uu____2458  in
        let all_lb_univs =
          let uu____2703 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2719 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2719) empty_set)
             in
          FStar_All.pipe_right uu____2703 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___265_2729 = s  in
        let uu____2730 =
          let uu____2731 =
            let uu____2738 =
              let uu____2739 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___266_2751 = lb  in
                        let uu____2752 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2755 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___266_2751.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2752;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___266_2751.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2755;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___266_2751.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___266_2751.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2739)  in
            (uu____2738, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2731  in
        {
          FStar_Syntax_Syntax.sigel = uu____2730;
          FStar_Syntax_Syntax.sigrng =
            (uu___265_2729.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___265_2729.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___265_2729.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___265_2729.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2763,fml) ->
        let uvs =
          let uu____2766 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2766 FStar_Util.set_elements  in
        let uu___267_2771 = s  in
        let uu____2772 =
          let uu____2773 =
            let uu____2780 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2780)  in
          FStar_Syntax_Syntax.Sig_assume uu____2773  in
        {
          FStar_Syntax_Syntax.sigel = uu____2772;
          FStar_Syntax_Syntax.sigrng =
            (uu___267_2771.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___267_2771.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___267_2771.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___267_2771.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2782,bs,c,flags1) ->
        let uvs =
          let uu____2791 =
            let uu____2794 = bs_univnames bs  in
            let uu____2797 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2794 uu____2797  in
          FStar_All.pipe_right uu____2791 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___268_2805 = s  in
        let uu____2806 =
          let uu____2807 =
            let uu____2820 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____2821 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2820, uu____2821, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2807  in
        {
          FStar_Syntax_Syntax.sigel = uu____2806;
          FStar_Syntax_Syntax.sigrng =
            (uu___268_2805.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___268_2805.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___268_2805.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___268_2805.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____2824 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___236_2829  ->
    match uu___236_2829 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2830 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2842 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2842)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2861 =
      let uu____2862 = unparen t  in uu____2862.FStar_Parser_AST.tm  in
    match uu____2861 with
    | FStar_Parser_AST.Wild  ->
        let uu____2867 =
          let uu____2868 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2868  in
        FStar_Util.Inr uu____2867
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2879)) ->
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
             let uu____2944 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2944
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2955 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2955
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2966 =
               let uu____2971 =
                 let uu____2972 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2972
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2971)
                in
             FStar_Errors.raise_error uu____2966 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2977 ->
        let rec aux t1 univargs =
          let uu____3011 =
            let uu____3012 = unparen t1  in uu____3012.FStar_Parser_AST.tm
             in
          match uu____3011 with
          | FStar_Parser_AST.App (t2,targ,uu____3019) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___237_3042  ->
                     match uu___237_3042 with
                     | FStar_Util.Inr uu____3047 -> true
                     | uu____3048 -> false) univargs
              then
                let uu____3053 =
                  let uu____3054 =
                    FStar_List.map
                      (fun uu___238_3063  ->
                         match uu___238_3063 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3054  in
                FStar_Util.Inr uu____3053
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___239_3080  ->
                        match uu___239_3080 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3086 -> failwith "impossible")
                     univargs
                    in
                 let uu____3087 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3087)
          | uu____3093 ->
              let uu____3094 =
                let uu____3099 =
                  let uu____3100 =
                    let uu____3101 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3101 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3100  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3099)  in
              FStar_Errors.raise_error uu____3094 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3110 ->
        let uu____3111 =
          let uu____3116 =
            let uu____3117 =
              let uu____3118 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3118 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3117  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3116)  in
        FStar_Errors.raise_error uu____3111 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____3151 ->
        let uu____3174 =
          let uu____3179 =
            let uu____3180 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____3180
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3179)  in
        FStar_Errors.raise_error uu____3174 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3190 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3190) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3218 = FStar_List.hd fields  in
        match uu____3218 with
        | (f,uu____3228) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3240 =
                match uu____3240 with
                | (f',uu____3246) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3248 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3248
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
              (let uu____3252 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3252);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____3641 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____3648 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____3649 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____3651,pats1) ->
                let aux out uu____3689 =
                  match uu____3689 with
                  | (p2,uu____3701) ->
                      let intersection =
                        let uu____3709 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3709 out  in
                      let uu____3712 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3712
                      then
                        let uu____3715 = pat_vars p2  in
                        FStar_Util.set_union out uu____3715
                      else
                        (let duplicate_bv =
                           let uu____3720 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3720  in
                         let uu____3723 =
                           let uu____3728 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3728)
                            in
                         FStar_Errors.raise_error uu____3723 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3748 = pat_vars p1  in
              FStar_All.pipe_right uu____3748 (fun a236  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3776 =
                  let uu____3777 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3777  in
                if uu____3776
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3784 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3784  in
                   let first_nonlinear_var =
                     let uu____3788 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3788  in
                   let uu____3791 =
                     let uu____3796 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3796)  in
                   FStar_Errors.raise_error uu____3791 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3800) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3801) -> ()
         | (true ,uu____3808) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3831 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____3831 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3847 ->
               let uu____3850 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____3850 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3962 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____3978 =
                 let uu____3979 =
                   let uu____3980 =
                     let uu____3987 =
                       let uu____3988 =
                         let uu____3993 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____3993, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____3988  in
                     (uu____3987, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____3980  in
                 {
                   FStar_Parser_AST.pat = uu____3979;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____3978
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____4010 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____4011 = aux loc env1 p2  in
                 match uu____4011 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___269_4069 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___270_4074 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___270_4074.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___270_4074.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___269_4069.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___271_4076 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___272_4081 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___272_4081.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___272_4081.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___271_4076.FStar_Syntax_Syntax.p)
                           }
                       | uu____4082 when top -> p4
                       | uu____4083 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____4086 =
                       match binder with
                       | LetBinder uu____4099 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____4119 = close_fun env1 t  in
                             desugar_term env1 uu____4119  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____4121 -> true)
                            then
                              (let uu____4122 =
                                 let uu____4127 =
                                   let uu____4128 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____4129 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____4130 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____4128 uu____4129 uu____4130
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____4127)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____4122)
                            else ();
                            (let uu____4132 = annot_pat_var p3 t1  in
                             (uu____4132,
                               (LocalBinder
                                  ((let uu___273_4138 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___273_4138.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___273_4138.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____4086 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4160 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4160, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4169 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4169, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4186 = resolvex loc env1 x  in
               (match uu____4186 with
                | (loc1,env2,xbv) ->
                    let uu____4208 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4208, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4225 = resolvex loc env1 x  in
               (match uu____4225 with
                | (loc1,env2,xbv) ->
                    let uu____4247 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4247, imp))
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
               let uu____4257 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4257, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____4279;_},args)
               ->
               let uu____4285 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____4326  ->
                        match uu____4326 with
                        | (loc1,env2,args1) ->
                            let uu____4374 = aux loc1 env2 arg  in
                            (match uu____4374 with
                             | (loc2,env3,uu____4403,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____4285 with
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
                    let uu____4473 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____4473, false))
           | FStar_Parser_AST.PatApp uu____4488 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____4510 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____4543  ->
                        match uu____4543 with
                        | (loc1,env2,pats1) ->
                            let uu____4575 = aux loc1 env2 pat  in
                            (match uu____4575 with
                             | (loc2,env3,uu____4600,pat1,uu____4602) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____4510 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____4645 =
                        let uu____4648 =
                          let uu____4655 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____4655  in
                        let uu____4656 =
                          let uu____4657 =
                            let uu____4670 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____4670, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____4657  in
                        FStar_All.pipe_left uu____4648 uu____4656  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____4702 =
                               let uu____4703 =
                                 let uu____4716 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____4716, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____4703  in
                             FStar_All.pipe_left (pos_r r) uu____4702) pats1
                        uu____4645
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
               let uu____4758 =
                 FStar_List.fold_left
                   (fun uu____4798  ->
                      fun p2  ->
                        match uu____4798 with
                        | (loc1,env2,pats) ->
                            let uu____4847 = aux loc1 env2 p2  in
                            (match uu____4847 with
                             | (loc2,env3,uu____4876,pat,uu____4878) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4758 with
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
                    let uu____4973 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____4973 with
                     | (constr,uu____4995) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____4998 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____5000 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____5000, false)))
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
                      (fun uu____5069  ->
                         match uu____5069 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____5099  ->
                         match uu____5099 with
                         | (f,uu____5105) ->
                             let uu____5106 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____5132  ->
                                       match uu____5132 with
                                       | (g,uu____5138) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____5106 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____5143,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____5150 =
                   let uu____5151 =
                     let uu____5158 =
                       let uu____5159 =
                         let uu____5160 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____5160  in
                       FStar_Parser_AST.mk_pattern uu____5159
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____5158, args)  in
                   FStar_Parser_AST.PatApp uu____5151  in
                 FStar_Parser_AST.mk_pattern uu____5150
                   p1.FStar_Parser_AST.prange
                  in
               let uu____5163 = aux loc env1 app  in
               (match uu____5163 with
                | (env2,e,b,p2,uu____5192) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____5220 =
                            let uu____5221 =
                              let uu____5234 =
                                let uu___274_5235 = fv  in
                                let uu____5236 =
                                  let uu____5239 =
                                    let uu____5240 =
                                      let uu____5247 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____5247)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____5240
                                     in
                                  FStar_Pervasives_Native.Some uu____5239  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___274_5235.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___274_5235.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____5236
                                }  in
                              (uu____5234, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____5221  in
                          FStar_All.pipe_left pos uu____5220
                      | uu____5274 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____5328 = aux' true loc env1 p2  in
               (match uu____5328 with
                | (loc1,env2,var,p3,uu____5355) ->
                    let uu____5360 =
                      FStar_List.fold_left
                        (fun uu____5392  ->
                           fun p4  ->
                             match uu____5392 with
                             | (loc2,env3,ps1) ->
                                 let uu____5425 = aux' true loc2 env3 p4  in
                                 (match uu____5425 with
                                  | (loc3,env4,uu____5450,p5,uu____5452) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____5360 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____5503 ->
               let uu____5504 = aux' true loc env1 p1  in
               (match uu____5504 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____5544 = aux_maybe_or env p  in
         match uu____5544 with
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
            let uu____5603 =
              let uu____5604 =
                let uu____5615 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____5615,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____5604  in
            (env, uu____5603, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____5643 =
                  let uu____5644 =
                    let uu____5649 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____5649, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____5644  in
                mklet uu____5643
            | FStar_Parser_AST.PatVar (x,uu____5651) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____5657);
                   FStar_Parser_AST.prange = uu____5658;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____5678 =
                  let uu____5679 =
                    let uu____5690 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____5691 =
                      let uu____5698 = desugar_term env t  in
                      (uu____5698, tacopt1)  in
                    (uu____5690, uu____5691)  in
                  LetBinder uu____5679  in
                (env, uu____5678, [])
            | uu____5709 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5719 = desugar_data_pat env p is_mut  in
             match uu____5719 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5748;
                       FStar_Syntax_Syntax.p = uu____5749;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5750;
                       FStar_Syntax_Syntax.p = uu____5751;_}::[] -> []
                   | uu____5752 -> p1  in
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
  fun uu____5759  ->
    fun env  ->
      fun pat  ->
        let uu____5762 = desugar_data_pat env pat false  in
        match uu____5762 with | (env1,uu____5778,pat1) -> (env1, pat1)

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
      let uu____5797 = desugar_term_aq env e  in
      match uu____5797 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____5814 = desugar_typ_aq env e  in
      match uu____5814 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5824  ->
        fun range  ->
          match uu____5824 with
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
              ((let uu____5834 =
                  let uu____5835 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5835  in
                if uu____5834
                then
                  let uu____5836 =
                    let uu____5841 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5841)  in
                  FStar_Errors.log_issue range uu____5836
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
                  let uu____5846 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____5846 range  in
                let lid1 =
                  let uu____5850 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____5850 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____5860) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5869 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____5869 range  in
                           let private_fv =
                             let uu____5871 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5871 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___275_5872 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___275_5872.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___275_5872.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5873 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5880 =
                        let uu____5885 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5885)
                         in
                      FStar_Errors.raise_error uu____5880 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____5901 =
                  let uu____5908 =
                    let uu____5909 =
                      let uu____5926 =
                        let uu____5937 =
                          let uu____5946 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____5946)  in
                        [uu____5937]  in
                      (lid1, uu____5926)  in
                    FStar_Syntax_Syntax.Tm_app uu____5909  in
                  FStar_Syntax_Syntax.mk uu____5908  in
                uu____5901 FStar_Pervasives_Native.None range))

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
            let uu____5995 =
              let uu____6004 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____6004 l  in
            match uu____5995 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____6059;
                              FStar_Syntax_Syntax.vars = uu____6060;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6087 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6087 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____6097 =
                                 let uu____6098 =
                                   let uu____6101 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____6101  in
                                 uu____6098.FStar_Syntax_Syntax.n  in
                               match uu____6097 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____6123))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____6124 -> msg
                             else msg  in
                           let uu____6126 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6126
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6129 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6129 " is deprecated"  in
                           let uu____6130 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6130
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____6131 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____6136 =
                      let uu____6137 =
                        let uu____6144 = mk_ref_read tm1  in
                        (uu____6144,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____6137  in
                    FStar_All.pipe_left mk1 uu____6136
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____6162 =
          let uu____6163 = unparen t  in uu____6163.FStar_Parser_AST.tm  in
        match uu____6162 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____6164; FStar_Ident.ident = uu____6165;
              FStar_Ident.nsstr = uu____6166; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____6169 ->
            let uu____6170 =
              let uu____6175 =
                let uu____6176 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____6176  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____6175)  in
            FStar_Errors.raise_error uu____6170 t.FStar_Parser_AST.range
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
          let uu___276_6271 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___276_6271.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___276_6271.FStar_Syntax_Syntax.vars)
          }  in
        let uu____6274 =
          let uu____6275 = unparen top  in uu____6275.FStar_Parser_AST.tm  in
        match uu____6274 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____6280 ->
            let uu____6287 = desugar_formula env top  in (uu____6287, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____6294 = desugar_formula env t  in (uu____6294, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____6301 = desugar_formula env t  in (uu____6301, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____6325 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____6325, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____6327 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____6327, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____6335 =
                let uu____6336 =
                  let uu____6343 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____6343, args)  in
                FStar_Parser_AST.Op uu____6336  in
              FStar_Parser_AST.mk_term uu____6335 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____6346 =
              let uu____6347 =
                let uu____6348 =
                  let uu____6355 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____6355, [e])  in
                FStar_Parser_AST.Op uu____6348  in
              FStar_Parser_AST.mk_term uu____6347 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____6346
        | FStar_Parser_AST.Op (op_star,uu____6359::uu____6360::[]) when
            (let uu____6365 = FStar_Ident.text_of_id op_star  in
             uu____6365 = "*") &&
              (let uu____6367 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____6367 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____6382;_},t1::t2::[])
                  ->
                  let uu____6387 = flatten1 t1  in
                  FStar_List.append uu____6387 [t2]
              | uu____6390 -> [t]  in
            let uu____6391 =
              let uu____6418 =
                let uu____6443 =
                  let uu____6446 = unparen top  in flatten1 uu____6446  in
                FStar_All.pipe_right uu____6443
                  (FStar_List.map
                     (fun t  ->
                        let uu____6483 = desugar_typ_aq env t  in
                        match uu____6483 with
                        | (t',aq) ->
                            let uu____6494 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____6494, aq)))
                 in
              FStar_All.pipe_right uu____6418 FStar_List.unzip  in
            (match uu____6391 with
             | (targs,aqs) ->
                 let uu____6613 =
                   let uu____6618 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____6618
                    in
                 (match uu____6613 with
                  | (tup,uu____6636) ->
                      let uu____6637 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____6637, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____6651 =
              let uu____6652 =
                let uu____6655 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____6655  in
              FStar_All.pipe_left setpos uu____6652  in
            (uu____6651, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____6667 =
              let uu____6672 =
                let uu____6673 =
                  let uu____6674 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____6674 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____6673  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____6672)  in
            FStar_Errors.raise_error uu____6667 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____6685 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____6685 with
             | FStar_Pervasives_Native.None  ->
                 let uu____6692 =
                   let uu____6697 =
                     let uu____6698 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____6698
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____6697)
                    in
                 FStar_Errors.raise_error uu____6692
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____6708 =
                     let uu____6735 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____6801 = desugar_term_aq env t  in
                               match uu____6801 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____6735 FStar_List.unzip  in
                   (match uu____6708 with
                    | (args1,aqs) ->
                        let uu____6944 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6944, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6960)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6975 =
              let uu___277_6976 = top  in
              let uu____6977 =
                let uu____6978 =
                  let uu____6985 =
                    let uu___278_6986 = top  in
                    let uu____6987 =
                      let uu____6988 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6988  in
                    {
                      FStar_Parser_AST.tm = uu____6987;
                      FStar_Parser_AST.range =
                        (uu___278_6986.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___278_6986.FStar_Parser_AST.level)
                    }  in
                  (uu____6985, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6978  in
              {
                FStar_Parser_AST.tm = uu____6977;
                FStar_Parser_AST.range =
                  (uu___277_6976.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___277_6976.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6975
        | FStar_Parser_AST.Construct (n1,(a,uu____6991)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____7007 =
                let uu___279_7008 = top  in
                let uu____7009 =
                  let uu____7010 =
                    let uu____7017 =
                      let uu___280_7018 = top  in
                      let uu____7019 =
                        let uu____7020 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____7020  in
                      {
                        FStar_Parser_AST.tm = uu____7019;
                        FStar_Parser_AST.range =
                          (uu___280_7018.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___280_7018.FStar_Parser_AST.level)
                      }  in
                    (uu____7017, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____7010  in
                {
                  FStar_Parser_AST.tm = uu____7009;
                  FStar_Parser_AST.range =
                    (uu___279_7008.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___279_7008.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____7007))
        | FStar_Parser_AST.Construct (n1,(a,uu____7023)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____7038 =
              let uu___281_7039 = top  in
              let uu____7040 =
                let uu____7041 =
                  let uu____7048 =
                    let uu___282_7049 = top  in
                    let uu____7050 =
                      let uu____7051 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____7051  in
                    {
                      FStar_Parser_AST.tm = uu____7050;
                      FStar_Parser_AST.range =
                        (uu___282_7049.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___282_7049.FStar_Parser_AST.level)
                    }  in
                  (uu____7048, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____7041  in
              {
                FStar_Parser_AST.tm = uu____7040;
                FStar_Parser_AST.range =
                  (uu___281_7039.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___281_7039.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____7038
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7052; FStar_Ident.ident = uu____7053;
              FStar_Ident.nsstr = uu____7054; FStar_Ident.str = "Type0";_}
            ->
            let uu____7057 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____7057, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7058; FStar_Ident.ident = uu____7059;
              FStar_Ident.nsstr = uu____7060; FStar_Ident.str = "Type";_}
            ->
            let uu____7063 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____7063, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____7064; FStar_Ident.ident = uu____7065;
               FStar_Ident.nsstr = uu____7066; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____7084 =
              let uu____7085 =
                let uu____7086 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____7086  in
              mk1 uu____7085  in
            (uu____7084, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7087; FStar_Ident.ident = uu____7088;
              FStar_Ident.nsstr = uu____7089; FStar_Ident.str = "Effect";_}
            ->
            let uu____7092 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____7092, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7093; FStar_Ident.ident = uu____7094;
              FStar_Ident.nsstr = uu____7095; FStar_Ident.str = "True";_}
            ->
            let uu____7098 =
              let uu____7099 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7099
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7098, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7100; FStar_Ident.ident = uu____7101;
              FStar_Ident.nsstr = uu____7102; FStar_Ident.str = "False";_}
            ->
            let uu____7105 =
              let uu____7106 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7106
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7105, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____7109;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____7111 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____7111 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____7120 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____7120, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____7121 =
                    let uu____7122 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____7122 txt
                     in
                  failwith uu____7121))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7129 = desugar_name mk1 setpos env true l  in
              (uu____7129, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7132 = desugar_name mk1 setpos env true l  in
              (uu____7132, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____7143 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____7143 with
                | FStar_Pervasives_Native.Some uu____7152 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____7157 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____7157 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____7171 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____7188 =
                    let uu____7189 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____7189  in
                  (uu____7188, noaqs)
              | uu____7190 ->
                  let uu____7197 =
                    let uu____7202 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____7202)  in
                  FStar_Errors.raise_error uu____7197
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____7209 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____7209 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7216 =
                    let uu____7221 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____7221)
                     in
                  FStar_Errors.raise_error uu____7216
                    top.FStar_Parser_AST.range
              | uu____7226 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____7230 = desugar_name mk1 setpos env true lid'  in
                  (uu____7230, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7246 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____7246 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____7265 ->
                       let uu____7272 =
                         FStar_Util.take
                           (fun uu____7296  ->
                              match uu____7296 with
                              | (uu____7301,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____7272 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____7346 =
                              let uu____7373 =
                                FStar_List.map
                                  (fun uu____7418  ->
                                     match uu____7418 with
                                     | (t,imp) ->
                                         let uu____7435 =
                                           desugar_term_aq env t  in
                                         (match uu____7435 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____7373
                                FStar_List.unzip
                               in
                            (match uu____7346 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____7586 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____7586, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____7604 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____7604 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____7611 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____7622 =
              FStar_List.fold_left
                (fun uu____7667  ->
                   fun b  ->
                     match uu____7667 with
                     | (env1,tparams,typs) ->
                         let uu____7724 = desugar_binder env1 b  in
                         (match uu____7724 with
                          | (xopt,t1) ->
                              let uu____7753 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____7762 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____7762)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____7753 with
                               | (env2,x) ->
                                   let uu____7782 =
                                     let uu____7785 =
                                       let uu____7788 =
                                         let uu____7789 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7789
                                          in
                                       [uu____7788]  in
                                     FStar_List.append typs uu____7785  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___283_7815 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___283_7815.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___283_7815.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____7782)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____7622 with
             | (env1,uu____7843,targs) ->
                 let uu____7865 =
                   let uu____7870 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7870
                    in
                 (match uu____7865 with
                  | (tup,uu____7880) ->
                      let uu____7881 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7881, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7900 = uncurry binders t  in
            (match uu____7900 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___240_7944 =
                   match uu___240_7944 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7960 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7960
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7984 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7984 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____8017 = aux env [] bs  in (uu____8017, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____8026 = desugar_binder env b  in
            (match uu____8026 with
             | (FStar_Pervasives_Native.None ,uu____8037) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____8051 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____8051 with
                  | ((x,uu____8067),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____8080 =
                        let uu____8081 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____8081  in
                      (uu____8080, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____8099 =
              FStar_List.fold_left
                (fun uu____8119  ->
                   fun pat  ->
                     match uu____8119 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____8145,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____8155 =
                                let uu____8158 = free_type_vars env1 t  in
                                FStar_List.append uu____8158 ftvs  in
                              (env1, uu____8155)
                          | FStar_Parser_AST.PatAscribed
                              (uu____8163,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____8174 =
                                let uu____8177 = free_type_vars env1 t  in
                                let uu____8180 =
                                  let uu____8183 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____8183 ftvs  in
                                FStar_List.append uu____8177 uu____8180  in
                              (env1, uu____8174)
                          | uu____8188 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____8099 with
             | (uu____8197,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____8209 =
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
                   FStar_List.append uu____8209 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___241_8266 =
                   match uu___241_8266 with
                   | [] ->
                       let uu____8293 = desugar_term_aq env1 body  in
                       (match uu____8293 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____8330 =
                                      let uu____8331 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____8331
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____8330 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____8400 =
                              let uu____8403 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____8403  in
                            (uu____8400, aq))
                   | p::rest ->
                       let uu____8418 = desugar_binding_pat env1 p  in
                       (match uu____8418 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____8454 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____8461 =
                              match b with
                              | LetBinder uu____8502 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____8570) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____8624 =
                                          let uu____8633 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____8633, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____8624
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____8695,uu____8696) ->
                                             let tup2 =
                                               let uu____8698 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8698
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8702 =
                                                 let uu____8709 =
                                                   let uu____8710 =
                                                     let uu____8727 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____8730 =
                                                       let uu____8741 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____8750 =
                                                         let uu____8761 =
                                                           let uu____8770 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____8770
                                                            in
                                                         [uu____8761]  in
                                                       uu____8741 ::
                                                         uu____8750
                                                        in
                                                     (uu____8727, uu____8730)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8710
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8709
                                                  in
                                               uu____8702
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____8821 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____8821
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____8864,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____8866,pats)) ->
                                             let tupn =
                                               let uu____8909 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8909
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8921 =
                                                 let uu____8922 =
                                                   let uu____8939 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____8942 =
                                                     let uu____8953 =
                                                       let uu____8964 =
                                                         let uu____8973 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____8973
                                                          in
                                                       [uu____8964]  in
                                                     FStar_List.append args
                                                       uu____8953
                                                      in
                                                   (uu____8939, uu____8942)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8922
                                                  in
                                               mk1 uu____8921  in
                                             let p2 =
                                               let uu____9021 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____9021
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____9062 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____8461 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____9155,uu____9156,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____9178 =
                let uu____9179 = unparen e  in uu____9179.FStar_Parser_AST.tm
                 in
              match uu____9178 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____9189 ->
                  let uu____9190 = desugar_term_aq env e  in
                  (match uu____9190 with
                   | (head1,aq) ->
                       let uu____9203 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____9203, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____9210 ->
            let rec aux args aqs e =
              let uu____9293 =
                let uu____9294 = unparen e  in uu____9294.FStar_Parser_AST.tm
                 in
              match uu____9293 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____9314 = desugar_term_aq env t  in
                  (match uu____9314 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____9366 ->
                  let uu____9367 = desugar_term_aq env e  in
                  (match uu____9367 with
                   | (head1,aq) ->
                       let uu____9390 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____9390, (join_aqs (aq :: aqs))))
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
            let uu____9456 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____9456
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
            let uu____9508 = desugar_term_aq env t  in
            (match uu____9508 with
             | (tm,s) ->
                 let uu____9519 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____9519, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____9525 =
              let uu____9538 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____9538 then desugar_typ_aq else desugar_term_aq  in
            uu____9525 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____9593 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____9736  ->
                        match uu____9736 with
                        | (attr_opt,(p,def)) ->
                            let uu____9794 = is_app_pattern p  in
                            if uu____9794
                            then
                              let uu____9825 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____9825, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____9907 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____9907, def1)
                               | uu____9952 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____9990);
                                           FStar_Parser_AST.prange =
                                             uu____9991;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____10039 =
                                            let uu____10060 =
                                              let uu____10065 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____10065  in
                                            (uu____10060, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____10039, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____10156) ->
                                        if top_level
                                        then
                                          let uu____10191 =
                                            let uu____10212 =
                                              let uu____10217 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____10217  in
                                            (uu____10212, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____10191, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____10307 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____10338 =
                FStar_List.fold_left
                  (fun uu____10411  ->
                     fun uu____10412  ->
                       match (uu____10411, uu____10412) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____10520,uu____10521),uu____10522))
                           ->
                           let uu____10639 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____10665 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____10665 with
                                  | (env2,xx) ->
                                      let uu____10684 =
                                        let uu____10687 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____10687 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____10684))
                             | FStar_Util.Inr l ->
                                 let uu____10695 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____10695, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____10639 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____10338 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____10843 =
                    match uu____10843 with
                    | (attrs_opt,(uu____10879,args,result_t),def) ->
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
                                let uu____10967 = is_comp_type env1 t  in
                                if uu____10967
                                then
                                  ((let uu____10969 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____10979 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____10979))
                                       in
                                    match uu____10969 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____10982 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____10984 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____10984))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____10982
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
                          | uu____10991 ->
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
                              let uu____11006 =
                                let uu____11007 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____11007
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____11006
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
                  let uu____11084 = desugar_term_aq env' body  in
                  (match uu____11084 with
                   | (body1,aq) ->
                       let uu____11097 =
                         let uu____11100 =
                           let uu____11101 =
                             let uu____11114 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____11114)  in
                           FStar_Syntax_Syntax.Tm_let uu____11101  in
                         FStar_All.pipe_left mk1 uu____11100  in
                       (uu____11097, aq))
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
              let uu____11194 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____11194 with
              | (env1,binder,pat1) ->
                  let uu____11216 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____11242 = desugar_term_aq env1 t2  in
                        (match uu____11242 with
                         | (body1,aq) ->
                             let fv =
                               let uu____11256 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____11256
                                 FStar_Pervasives_Native.None
                                in
                             let uu____11257 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____11257, aq))
                    | LocalBinder (x,uu____11287) ->
                        let uu____11288 = desugar_term_aq env1 t2  in
                        (match uu____11288 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____11302;
                                   FStar_Syntax_Syntax.p = uu____11303;_}::[]
                                   -> body1
                               | uu____11304 ->
                                   let uu____11307 =
                                     let uu____11314 =
                                       let uu____11315 =
                                         let uu____11338 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____11341 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____11338, uu____11341)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11315
                                        in
                                     FStar_Syntax_Syntax.mk uu____11314  in
                                   uu____11307 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____11381 =
                               let uu____11384 =
                                 let uu____11385 =
                                   let uu____11398 =
                                     let uu____11401 =
                                       let uu____11402 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____11402]  in
                                     FStar_Syntax_Subst.close uu____11401
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____11398)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____11385  in
                               FStar_All.pipe_left mk1 uu____11384  in
                             (uu____11381, aq))
                     in
                  (match uu____11216 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____11465 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____11465, aq)
                       else (tm, aq))
               in
            let uu____11477 = FStar_List.hd lbs  in
            (match uu____11477 with
             | (attrs,(head_pat,defn)) ->
                 let uu____11521 = is_rec || (is_app_pattern head_pat)  in
                 if uu____11521
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____11534 =
                let uu____11535 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____11535  in
              mk1 uu____11534  in
            let uu____11536 = desugar_term_aq env t1  in
            (match uu____11536 with
             | (t1',aq1) ->
                 let uu____11547 = desugar_term_aq env t2  in
                 (match uu____11547 with
                  | (t2',aq2) ->
                      let uu____11558 = desugar_term_aq env t3  in
                      (match uu____11558 with
                       | (t3',aq3) ->
                           let uu____11569 =
                             let uu____11570 =
                               let uu____11571 =
                                 let uu____11594 =
                                   let uu____11611 =
                                     let uu____11626 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____11626,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____11639 =
                                     let uu____11656 =
                                       let uu____11671 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____11671,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____11656]  in
                                   uu____11611 :: uu____11639  in
                                 (t1', uu____11594)  in
                               FStar_Syntax_Syntax.Tm_match uu____11571  in
                             mk1 uu____11570  in
                           (uu____11569, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____11870 =
              match uu____11870 with
              | (pat,wopt,b) ->
                  let uu____11892 = desugar_match_pat env pat  in
                  (match uu____11892 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____11923 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____11923
                          in
                       let uu____11928 = desugar_term_aq env1 b  in
                       (match uu____11928 with
                        | (b1,aq) ->
                            let uu____11941 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____11941, aq)))
               in
            let uu____11946 = desugar_term_aq env e  in
            (match uu____11946 with
             | (e1,aq) ->
                 let uu____11957 =
                   let uu____11990 =
                     let uu____12025 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____12025 FStar_List.unzip  in
                   FStar_All.pipe_right uu____11990
                     (fun uu____12257  ->
                        match uu____12257 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____11957 with
                  | (brs,aqs) ->
                      let uu____12490 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____12490, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____12535 = is_comp_type env t  in
              if uu____12535
              then
                let uu____12544 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____12544
              else
                (let uu____12552 = desugar_term env t  in
                 FStar_Util.Inl uu____12552)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____12566 = desugar_term_aq env e  in
            (match uu____12566 with
             | (e1,aq) ->
                 let uu____12577 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____12577, aq))
        | FStar_Parser_AST.Record (uu____12610,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____12651 = FStar_List.hd fields  in
              match uu____12651 with | (f,uu____12663) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____12709  ->
                        match uu____12709 with
                        | (g,uu____12715) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____12721,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____12735 =
                         let uu____12740 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____12740)
                          in
                       FStar_Errors.raise_error uu____12735
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
                  let uu____12748 =
                    let uu____12759 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____12790  ->
                              match uu____12790 with
                              | (f,uu____12800) ->
                                  let uu____12801 =
                                    let uu____12802 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____12802
                                     in
                                  (uu____12801, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____12759)  in
                  FStar_Parser_AST.Construct uu____12748
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____12820 =
                      let uu____12821 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____12821  in
                    FStar_Parser_AST.mk_term uu____12820
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____12823 =
                      let uu____12836 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____12866  ->
                                match uu____12866 with
                                | (f,uu____12876) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____12836)  in
                    FStar_Parser_AST.Record uu____12823  in
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
            let uu____12936 = desugar_term_aq env recterm1  in
            (match uu____12936 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____12952;
                         FStar_Syntax_Syntax.vars = uu____12953;_},args)
                      ->
                      let uu____12979 =
                        let uu____12980 =
                          let uu____12981 =
                            let uu____12998 =
                              let uu____13001 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____13002 =
                                let uu____13005 =
                                  let uu____13006 =
                                    let uu____13013 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____13013)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____13006
                                   in
                                FStar_Pervasives_Native.Some uu____13005  in
                              FStar_Syntax_Syntax.fvar uu____13001
                                FStar_Syntax_Syntax.delta_constant
                                uu____13002
                               in
                            (uu____12998, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____12981  in
                        FStar_All.pipe_left mk1 uu____12980  in
                      (uu____12979, s)
                  | uu____13042 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____13046 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____13046 with
              | (constrname,is_rec) ->
                  let uu____13061 = desugar_term_aq env e  in
                  (match uu____13061 with
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
                       let uu____13079 =
                         let uu____13080 =
                           let uu____13081 =
                             let uu____13098 =
                               let uu____13101 =
                                 let uu____13102 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____13102
                                  in
                               FStar_Syntax_Syntax.fvar uu____13101
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____13103 =
                               let uu____13114 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____13114]  in
                             (uu____13098, uu____13103)  in
                           FStar_Syntax_Syntax.Tm_app uu____13081  in
                         FStar_All.pipe_left mk1 uu____13080  in
                       (uu____13079, s))))
        | FStar_Parser_AST.NamedTyp (uu____13151,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____13160 =
              let uu____13161 = FStar_Syntax_Subst.compress tm  in
              uu____13161.FStar_Syntax_Syntax.n  in
            (match uu____13160 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____13169 =
                   let uu___284_13170 =
                     let uu____13171 =
                       let uu____13172 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____13172  in
                     FStar_Syntax_Util.exp_string uu____13171  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___284_13170.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___284_13170.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____13169, noaqs)
             | uu____13173 ->
                 let uu____13174 =
                   let uu____13179 =
                     let uu____13180 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____13180
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____13179)  in
                 FStar_Errors.raise_error uu____13174
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____13186 = desugar_term_aq env e  in
            (match uu____13186 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____13198 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____13198, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____13204 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____13205 =
              let uu____13206 =
                let uu____13215 = desugar_term env e  in (bv, b, uu____13215)
                 in
              [uu____13206]  in
            (uu____13204, uu____13205)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____13246 =
              let uu____13247 =
                let uu____13248 =
                  let uu____13255 = desugar_term env e  in (uu____13255, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____13248  in
              FStar_All.pipe_left mk1 uu____13247  in
            (uu____13246, noaqs)
        | uu____13260 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____13261 = desugar_formula env top  in
            (uu____13261, noaqs)
        | uu____13262 ->
            let uu____13263 =
              let uu____13268 =
                let uu____13269 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____13269  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____13268)  in
            FStar_Errors.raise_error uu____13263 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____13275 -> false
    | uu____13284 -> true

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
           (fun uu____13321  ->
              match uu____13321 with
              | (a,imp) ->
                  let uu____13334 = desugar_term env a  in
                  arg_withimp_e imp uu____13334))

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
        let is_requires uu____13366 =
          match uu____13366 with
          | (t1,uu____13372) ->
              let uu____13373 =
                let uu____13374 = unparen t1  in
                uu____13374.FStar_Parser_AST.tm  in
              (match uu____13373 with
               | FStar_Parser_AST.Requires uu____13375 -> true
               | uu____13382 -> false)
           in
        let is_ensures uu____13392 =
          match uu____13392 with
          | (t1,uu____13398) ->
              let uu____13399 =
                let uu____13400 = unparen t1  in
                uu____13400.FStar_Parser_AST.tm  in
              (match uu____13399 with
               | FStar_Parser_AST.Ensures uu____13401 -> true
               | uu____13408 -> false)
           in
        let is_app head1 uu____13423 =
          match uu____13423 with
          | (t1,uu____13429) ->
              let uu____13430 =
                let uu____13431 = unparen t1  in
                uu____13431.FStar_Parser_AST.tm  in
              (match uu____13430 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____13433;
                      FStar_Parser_AST.level = uu____13434;_},uu____13435,uu____13436)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____13437 -> false)
           in
        let is_smt_pat uu____13447 =
          match uu____13447 with
          | (t1,uu____13453) ->
              let uu____13454 =
                let uu____13455 = unparen t1  in
                uu____13455.FStar_Parser_AST.tm  in
              (match uu____13454 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____13458);
                             FStar_Parser_AST.range = uu____13459;
                             FStar_Parser_AST.level = uu____13460;_},uu____13461)::uu____13462::[])
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
                             FStar_Parser_AST.range = uu____13501;
                             FStar_Parser_AST.level = uu____13502;_},uu____13503)::uu____13504::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____13529 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____13561 = head_and_args t1  in
          match uu____13561 with
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
                   let thunk_ens uu____13659 =
                     match uu____13659 with
                     | (e,i) ->
                         let uu____13670 = thunk_ens_ e  in (uu____13670, i)
                      in
                   let fail_lemma uu____13682 =
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
                         let uu____13762 =
                           let uu____13769 =
                             let uu____13776 = thunk_ens ens  in
                             [uu____13776; nil_pat]  in
                           req_true :: uu____13769  in
                         unit_tm :: uu____13762
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____13823 =
                           let uu____13830 =
                             let uu____13837 = thunk_ens ens  in
                             [uu____13837; nil_pat]  in
                           req :: uu____13830  in
                         unit_tm :: uu____13823
                     | ens::smtpat::[] when
                         (((let uu____13886 = is_requires ens  in
                            Prims.op_Negation uu____13886) &&
                             (let uu____13888 = is_smt_pat ens  in
                              Prims.op_Negation uu____13888))
                            &&
                            (let uu____13890 = is_decreases ens  in
                             Prims.op_Negation uu____13890))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____13891 =
                           let uu____13898 =
                             let uu____13905 = thunk_ens ens  in
                             [uu____13905; smtpat]  in
                           req_true :: uu____13898  in
                         unit_tm :: uu____13891
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____13952 =
                           let uu____13959 =
                             let uu____13966 = thunk_ens ens  in
                             [uu____13966; nil_pat; dec]  in
                           req_true :: uu____13959  in
                         unit_tm :: uu____13952
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____14026 =
                           let uu____14033 =
                             let uu____14040 = thunk_ens ens  in
                             [uu____14040; smtpat; dec]  in
                           req_true :: uu____14033  in
                         unit_tm :: uu____14026
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____14100 =
                           let uu____14107 =
                             let uu____14114 = thunk_ens ens  in
                             [uu____14114; nil_pat; dec]  in
                           req :: uu____14107  in
                         unit_tm :: uu____14100
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____14174 =
                           let uu____14181 =
                             let uu____14188 = thunk_ens ens  in
                             [uu____14188; smtpat]  in
                           req :: uu____14181  in
                         unit_tm :: uu____14174
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____14253 =
                           let uu____14260 =
                             let uu____14267 = thunk_ens ens  in
                             [uu____14267; dec; smtpat]  in
                           req :: uu____14260  in
                         unit_tm :: uu____14253
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____14329 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____14329, args)
               | FStar_Parser_AST.Name l when
                   (let uu____14357 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____14357
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____14358 =
                     let uu____14365 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14365, [])  in
                   (uu____14358, args)
               | FStar_Parser_AST.Name l when
                   (let uu____14383 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____14383
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____14384 =
                     let uu____14391 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14391, [])  in
                   (uu____14384, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____14407 =
                     let uu____14414 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14414, [])  in
                   (uu____14407, [(t1, FStar_Parser_AST.Nothing)])
               | uu____14437 ->
                   let default_effect =
                     let uu____14439 = FStar_Options.ml_ish ()  in
                     if uu____14439
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____14442 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____14442
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____14444 =
                     let uu____14451 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____14451, [])  in
                   (uu____14444, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____14474 = pre_process_comp_typ t  in
        match uu____14474 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____14523 =
                  let uu____14528 =
                    let uu____14529 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____14529
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____14528)  in
                fail1 uu____14523)
             else ();
             (let is_universe uu____14540 =
                match uu____14540 with
                | (uu____14545,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____14547 = FStar_Util.take is_universe args  in
              match uu____14547 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____14606  ->
                         match uu____14606 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____14613 =
                    let uu____14628 = FStar_List.hd args1  in
                    let uu____14637 = FStar_List.tl args1  in
                    (uu____14628, uu____14637)  in
                  (match uu____14613 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____14692 =
                         let is_decrease uu____14730 =
                           match uu____14730 with
                           | (t1,uu____14740) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____14750;
                                       FStar_Syntax_Syntax.vars = uu____14751;_},uu____14752::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____14791 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____14692 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____14907  ->
                                      match uu____14907 with
                                      | (t1,uu____14917) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____14926,(arg,uu____14928)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____14967 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____14984 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____14995 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____14995
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____14999 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____14999
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____15006 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____15006
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____15010 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____15010
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____15014 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____15014
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____15018 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____15018
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____15036 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____15036
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
                                                  let uu____15125 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____15125
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
                                            | uu____15146 -> pat  in
                                          let uu____15147 =
                                            let uu____15158 =
                                              let uu____15169 =
                                                let uu____15178 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____15178, aq)  in
                                              [uu____15169]  in
                                            ens :: uu____15158  in
                                          req :: uu____15147
                                      | uu____15219 -> rest2
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
        | uu____15243 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___285_15264 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___285_15264.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___285_15264.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___286_15306 = b  in
             {
               FStar_Parser_AST.b = (uu___286_15306.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___286_15306.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___286_15306.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____15369 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____15369)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____15382 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____15382 with
             | (env1,a1) ->
                 let a2 =
                   let uu___287_15392 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___287_15392.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___287_15392.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____15418 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____15432 =
                     let uu____15435 =
                       let uu____15436 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____15436]  in
                     no_annot_abs uu____15435 body2  in
                   FStar_All.pipe_left setpos uu____15432  in
                 let uu____15457 =
                   let uu____15458 =
                     let uu____15475 =
                       let uu____15478 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____15478
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____15479 =
                       let uu____15490 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____15490]  in
                     (uu____15475, uu____15479)  in
                   FStar_Syntax_Syntax.Tm_app uu____15458  in
                 FStar_All.pipe_left mk1 uu____15457)
        | uu____15529 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____15609 = q (rest, pats, body)  in
              let uu____15616 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____15609 uu____15616
                FStar_Parser_AST.Formula
               in
            let uu____15617 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____15617 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____15626 -> failwith "impossible"  in
      let uu____15629 =
        let uu____15630 = unparen f  in uu____15630.FStar_Parser_AST.tm  in
      match uu____15629 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____15637,uu____15638) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____15649,uu____15650) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15681 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____15681
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15717 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____15717
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____15760 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____15765 =
        FStar_List.fold_left
          (fun uu____15798  ->
             fun b  ->
               match uu____15798 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___288_15842 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___288_15842.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___288_15842.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___288_15842.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15857 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____15857 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___289_15875 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___289_15875.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___289_15875.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____15876 =
                               let uu____15883 =
                                 let uu____15888 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____15888)  in
                               uu____15883 :: out  in
                             (env2, uu____15876))
                    | uu____15899 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____15765 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____15970 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15970)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____15975 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15975)
      | FStar_Parser_AST.TVariable x ->
          let uu____15979 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____15979)
      | FStar_Parser_AST.NoName t ->
          let uu____15983 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____15983)
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
      fun uu___242_15991  ->
        match uu___242_15991 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____16013 = FStar_Syntax_Syntax.null_binder k  in
            (uu____16013, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16030 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16030 with
             | (env1,a1) ->
                 let uu____16047 =
                   let uu____16054 = trans_aqual env1 imp  in
                   ((let uu___290_16060 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___290_16060.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___290_16060.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____16054)
                    in
                 (uu____16047, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___243_16068  ->
      match uu___243_16068 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____16072 =
            let uu____16073 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____16073  in
          FStar_Pervasives_Native.Some uu____16072
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
               (fun uu___244_16109  ->
                  match uu___244_16109 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____16110 -> false))
           in
        let quals2 q =
          let uu____16123 =
            (let uu____16126 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____16126) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____16123
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____16140 = FStar_Ident.range_of_lid disc_name  in
                let uu____16141 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____16140;
                  FStar_Syntax_Syntax.sigquals = uu____16141;
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
            let uu____16180 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____16218  ->
                        match uu____16218 with
                        | (x,uu____16228) ->
                            let uu____16233 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____16233 with
                             | (field_name,uu____16241) ->
                                 let only_decl =
                                   ((let uu____16245 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____16245)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____16247 =
                                        let uu____16248 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____16248.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____16247)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____16264 =
                                       FStar_List.filter
                                         (fun uu___245_16268  ->
                                            match uu___245_16268 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____16269 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____16264
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___246_16282  ->
                                             match uu___246_16282 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____16283 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____16285 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____16285;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____16290 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____16290
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____16295 =
                                        let uu____16300 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____16300  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____16295;
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
                                      let uu____16304 =
                                        let uu____16305 =
                                          let uu____16312 =
                                            let uu____16315 =
                                              let uu____16316 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____16316
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____16315]  in
                                          ((false, [lb]), uu____16312)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____16305
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____16304;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____16180 FStar_List.flatten
  
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
            (lid,uu____16360,t,uu____16362,n1,uu____16364) when
            let uu____16369 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____16369 ->
            let uu____16370 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____16370 with
             | (formals,uu____16388) ->
                 (match formals with
                  | [] -> []
                  | uu____16417 ->
                      let filter_records uu___247_16433 =
                        match uu___247_16433 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____16436,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____16448 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____16450 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____16450 with
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
                      let uu____16460 = FStar_Util.first_N n1 formals  in
                      (match uu____16460 with
                       | (uu____16489,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____16523 -> []
  
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
                    let uu____16601 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____16601
                    then
                      let uu____16604 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____16604
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____16607 =
                      let uu____16612 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____16612  in
                    let uu____16613 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____16618 =
                          let uu____16621 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____16621  in
                        FStar_Syntax_Util.arrow typars uu____16618
                      else FStar_Syntax_Syntax.tun  in
                    let uu____16625 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____16607;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____16613;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____16625;
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
          let tycon_id uu___248_16676 =
            match uu___248_16676 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____16678,uu____16679) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____16689,uu____16690,uu____16691) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____16701,uu____16702,uu____16703) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____16733,uu____16734,uu____16735) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____16779) ->
                let uu____16780 =
                  let uu____16781 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16781  in
                FStar_Parser_AST.mk_term uu____16780 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____16783 =
                  let uu____16784 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16784  in
                FStar_Parser_AST.mk_term uu____16783 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____16786) ->
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
              | uu____16817 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____16825 =
                     let uu____16826 =
                       let uu____16833 = binder_to_term b  in
                       (out, uu____16833, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____16826  in
                   FStar_Parser_AST.mk_term uu____16825
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___249_16845 =
            match uu___249_16845 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____16901  ->
                       match uu____16901 with
                       | (x,t,uu____16912) ->
                           let uu____16917 =
                             let uu____16918 =
                               let uu____16923 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____16923, t)  in
                             FStar_Parser_AST.Annotated uu____16918  in
                           FStar_Parser_AST.mk_binder uu____16917
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____16925 =
                    let uu____16926 =
                      let uu____16927 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____16927  in
                    FStar_Parser_AST.mk_term uu____16926
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____16925 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____16931 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____16958  ->
                          match uu____16958 with
                          | (x,uu____16968,uu____16969) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____16931)
            | uu____17022 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___250_17061 =
            match uu___250_17061 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____17085 = typars_of_binders _env binders  in
                (match uu____17085 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____17121 =
                         let uu____17122 =
                           let uu____17123 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____17123  in
                         FStar_Parser_AST.mk_term uu____17122
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____17121 binders  in
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
            | uu____17134 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____17176 =
              FStar_List.fold_left
                (fun uu____17210  ->
                   fun uu____17211  ->
                     match (uu____17210, uu____17211) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____17280 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____17280 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____17176 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____17371 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____17371
                | uu____17372 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____17380 = desugar_abstract_tc quals env [] tc  in
              (match uu____17380 with
               | (uu____17393,uu____17394,se,uu____17396) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____17399,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____17416 =
                                 let uu____17417 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____17417  in
                               if uu____17416
                               then
                                 let uu____17418 =
                                   let uu____17423 =
                                     let uu____17424 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____17424
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____17423)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____17418
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
                           | uu____17433 ->
                               let uu____17434 =
                                 let uu____17441 =
                                   let uu____17442 =
                                     let uu____17457 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____17457)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____17442
                                    in
                                 FStar_Syntax_Syntax.mk uu____17441  in
                               uu____17434 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___291_17473 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___291_17473.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___291_17473.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___291_17473.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____17474 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____17477 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____17477
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____17490 = typars_of_binders env binders  in
              (match uu____17490 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17524 =
                           FStar_Util.for_some
                             (fun uu___251_17526  ->
                                match uu___251_17526 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____17527 -> false) quals
                            in
                         if uu____17524
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____17532 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____17532
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____17537 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___252_17541  ->
                               match uu___252_17541 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____17542 -> false))
                        in
                     if uu____17537
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____17551 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____17551
                     then
                       let uu____17554 =
                         let uu____17561 =
                           let uu____17562 = unparen t  in
                           uu____17562.FStar_Parser_AST.tm  in
                         match uu____17561 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____17583 =
                               match FStar_List.rev args with
                               | (last_arg,uu____17613)::args_rev ->
                                   let uu____17625 =
                                     let uu____17626 = unparen last_arg  in
                                     uu____17626.FStar_Parser_AST.tm  in
                                   (match uu____17625 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____17654 -> ([], args))
                               | uu____17663 -> ([], args)  in
                             (match uu____17583 with
                              | (cattributes,args1) ->
                                  let uu____17702 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____17702))
                         | uu____17713 -> (t, [])  in
                       match uu____17554 with
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
                                  (fun uu___253_17735  ->
                                     match uu___253_17735 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____17736 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____17743)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____17767 = tycon_record_as_variant trec  in
              (match uu____17767 with
               | (t,fs) ->
                   let uu____17784 =
                     let uu____17787 =
                       let uu____17788 =
                         let uu____17797 =
                           let uu____17800 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____17800  in
                         (uu____17797, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____17788  in
                     uu____17787 :: quals  in
                   desugar_tycon env d uu____17784 [t])
          | uu____17805::uu____17806 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____17973 = et  in
                match uu____17973 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____18198 ->
                         let trec = tc  in
                         let uu____18222 = tycon_record_as_variant trec  in
                         (match uu____18222 with
                          | (t,fs) ->
                              let uu____18281 =
                                let uu____18284 =
                                  let uu____18285 =
                                    let uu____18294 =
                                      let uu____18297 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____18297  in
                                    (uu____18294, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____18285
                                   in
                                uu____18284 :: quals1  in
                              collect_tcs uu____18281 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____18384 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____18384 with
                          | (env2,uu____18444,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____18593 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____18593 with
                          | (env2,uu____18653,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____18778 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____18825 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____18825 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___255_19330  ->
                             match uu___255_19330 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____19395,uu____19396);
                                    FStar_Syntax_Syntax.sigrng = uu____19397;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____19398;
                                    FStar_Syntax_Syntax.sigmeta = uu____19399;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____19400;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____19463 =
                                     typars_of_binders env1 binders  in
                                   match uu____19463 with
                                   | (env2,tpars1) ->
                                       let uu____19490 =
                                         push_tparams env2 tpars1  in
                                       (match uu____19490 with
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
                                 let uu____19519 =
                                   let uu____19538 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____19538)
                                    in
                                 [uu____19519]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____19598);
                                    FStar_Syntax_Syntax.sigrng = uu____19599;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____19601;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____19602;_},constrs,tconstr,quals1)
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
                                 let uu____19700 = push_tparams env1 tpars
                                    in
                                 (match uu____19700 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____19767  ->
                                             match uu____19767 with
                                             | (x,uu____19779) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____19783 =
                                        let uu____19810 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____19918  ->
                                                  match uu____19918 with
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
                                                        let uu____19972 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____19972
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
                                                                uu___254_19983
                                                                 ->
                                                                match uu___254_19983
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____19995
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____20003 =
                                                        let uu____20022 =
                                                          let uu____20023 =
                                                            let uu____20024 =
                                                              let uu____20039
                                                                =
                                                                let uu____20040
                                                                  =
                                                                  let uu____20043
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____20043
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____20040
                                                                 in
                                                              (name, univs1,
                                                                uu____20039,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____20024
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____20023;
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
                                                          uu____20022)
                                                         in
                                                      (name, uu____20003)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____19810
                                         in
                                      (match uu____19783 with
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
                             | uu____20258 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____20384  ->
                             match uu____20384 with
                             | (name_doc,uu____20410,uu____20411) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____20483  ->
                             match uu____20483 with
                             | (uu____20502,uu____20503,se) -> se))
                      in
                   let uu____20529 =
                     let uu____20536 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____20536 rng
                      in
                   (match uu____20529 with
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
                               (fun uu____20598  ->
                                  match uu____20598 with
                                  | (uu____20619,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____20666,tps,k,uu____20669,constrs)
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
                                  | uu____20688 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____20705  ->
                                 match uu____20705 with
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
      let uu____20748 =
        FStar_List.fold_left
          (fun uu____20783  ->
             fun b  ->
               match uu____20783 with
               | (env1,binders1) ->
                   let uu____20827 = desugar_binder env1 b  in
                   (match uu____20827 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____20850 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____20850 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____20903 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____20748 with
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
          let uu____21004 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___256_21009  ->
                    match uu___256_21009 with
                    | FStar_Syntax_Syntax.Reflectable uu____21010 -> true
                    | uu____21011 -> false))
             in
          if uu____21004
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____21014 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____21014
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
      let uu____21046 = FStar_Syntax_Util.head_and_args at1  in
      match uu____21046 with
      | (hd1,args) ->
          let uu____21097 =
            let uu____21112 =
              let uu____21113 = FStar_Syntax_Subst.compress hd1  in
              uu____21113.FStar_Syntax_Syntax.n  in
            (uu____21112, args)  in
          (match uu____21097 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____21136)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr
               ->
               let uu____21171 =
                 let uu____21176 =
                   FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_int
                    in
                 FStar_Syntax_Embeddings.unembed uu____21176 a1  in
               (match uu____21171 with
                | FStar_Pervasives_Native.Some [] ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Error_EmptyFailErrs,
                        "Found ill-applied fail, argument should be a non-empty list of integers")
                      at1.FStar_Syntax_Syntax.pos
                | FStar_Pervasives_Native.Some es ->
                    let uu____21206 =
                      let uu____21213 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____21213, false)  in
                    FStar_Pervasives_Native.Some uu____21206
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____21262) when
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
           | uu____21318 -> FStar_Pervasives_Native.None)
  
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
                  let uu____21487 = desugar_binders monad_env eff_binders  in
                  match uu____21487 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____21526 =
                          let uu____21527 =
                            let uu____21536 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____21536  in
                          FStar_List.length uu____21527  in
                        uu____21526 = (Prims.parse_int "1")  in
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
                            (uu____21582,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____21584,uu____21585,uu____21586),uu____21587)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____21620 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____21621 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____21633 = name_of_eff_decl decl  in
                             FStar_List.mem uu____21633 mandatory_members)
                          eff_decls
                         in
                      (match uu____21621 with
                       | (mandatory_members_decls,actions) ->
                           let uu____21650 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____21679  ->
                                     fun decl  ->
                                       match uu____21679 with
                                       | (env2,out) ->
                                           let uu____21699 =
                                             desugar_decl env2 decl  in
                                           (match uu____21699 with
                                            | (env3,ses) ->
                                                let uu____21712 =
                                                  let uu____21715 =
                                                    FStar_List.hd ses  in
                                                  uu____21715 :: out  in
                                                (env3, uu____21712)))
                                  (env1, []))
                              in
                           (match uu____21650 with
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
                                              (uu____21783,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21786,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____21787,
                                                                  (def,uu____21789)::
                                                                  (cps_type,uu____21791)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____21792;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____21793;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____21845 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21845 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21883 =
                                                     let uu____21884 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21885 =
                                                       let uu____21886 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21886
                                                        in
                                                     let uu____21893 =
                                                       let uu____21894 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21894
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21884;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21885;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____21893
                                                     }  in
                                                   (uu____21883, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____21903,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21906,defn),doc1)::[])
                                              when for_free ->
                                              let uu____21941 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21941 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21979 =
                                                     let uu____21980 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21981 =
                                                       let uu____21982 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21982
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21980;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21981;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____21979, doc1))
                                          | uu____21991 ->
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
                                    let uu____22023 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____22023
                                     in
                                  let uu____22024 =
                                    let uu____22025 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____22025
                                     in
                                  ([], uu____22024)  in
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
                                      let uu____22042 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____22042)  in
                                    let uu____22049 =
                                      let uu____22050 =
                                        let uu____22051 =
                                          let uu____22052 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22052
                                           in
                                        let uu____22061 = lookup1 "return"
                                           in
                                        let uu____22062 = lookup1 "bind"  in
                                        let uu____22063 =
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
                                            uu____22051;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____22061;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____22062;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____22063
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____22050
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____22049;
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
                                         (fun uu___257_22069  ->
                                            match uu___257_22069 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____22070 -> true
                                            | uu____22071 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____22085 =
                                       let uu____22086 =
                                         let uu____22087 =
                                           lookup1 "return_wp"  in
                                         let uu____22088 = lookup1 "bind_wp"
                                            in
                                         let uu____22089 =
                                           lookup1 "if_then_else"  in
                                         let uu____22090 = lookup1 "ite_wp"
                                            in
                                         let uu____22091 = lookup1 "stronger"
                                            in
                                         let uu____22092 = lookup1 "close_wp"
                                            in
                                         let uu____22093 = lookup1 "assert_p"
                                            in
                                         let uu____22094 = lookup1 "assume_p"
                                            in
                                         let uu____22095 = lookup1 "null_wp"
                                            in
                                         let uu____22096 = lookup1 "trivial"
                                            in
                                         let uu____22097 =
                                           if rr
                                           then
                                             let uu____22098 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____22098
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____22114 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____22116 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____22118 =
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
                                             uu____22087;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____22088;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____22089;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____22090;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____22091;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____22092;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____22093;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____22094;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____22095;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____22096;
                                           FStar_Syntax_Syntax.repr =
                                             uu____22097;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____22114;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____22116;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____22118
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____22086
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____22085;
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
                                          fun uu____22144  ->
                                            match uu____22144 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____22158 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____22158
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
                let uu____22182 = desugar_binders env1 eff_binders  in
                match uu____22182 with
                | (env2,binders) ->
                    let uu____22219 =
                      let uu____22230 = head_and_args defn  in
                      match uu____22230 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____22267 ->
                                let uu____22268 =
                                  let uu____22273 =
                                    let uu____22274 =
                                      let uu____22275 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____22275 " not found"
                                       in
                                    Prims.strcat "Effect " uu____22274  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____22273)
                                   in
                                FStar_Errors.raise_error uu____22268
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____22277 =
                            match FStar_List.rev args with
                            | (last_arg,uu____22307)::args_rev ->
                                let uu____22319 =
                                  let uu____22320 = unparen last_arg  in
                                  uu____22320.FStar_Parser_AST.tm  in
                                (match uu____22319 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____22348 -> ([], args))
                            | uu____22357 -> ([], args)  in
                          (match uu____22277 with
                           | (cattributes,args1) ->
                               let uu____22400 = desugar_args env2 args1  in
                               let uu____22401 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____22400, uu____22401))
                       in
                    (match uu____22219 with
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
                          (let uu____22437 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____22437 with
                           | (ed_binders,uu____22451,ed_binders_opening) ->
                               let sub1 uu____22464 =
                                 match uu____22464 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____22478 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____22478 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____22482 =
                                       let uu____22483 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____22483)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____22482
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____22492 =
                                   let uu____22493 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____22493
                                    in
                                 let uu____22508 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____22509 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____22510 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____22511 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____22512 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____22513 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____22514 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____22515 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____22516 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____22517 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____22518 =
                                   let uu____22519 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____22519
                                    in
                                 let uu____22534 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____22535 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____22536 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____22544 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____22545 =
                                          let uu____22546 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22546
                                           in
                                        let uu____22561 =
                                          let uu____22562 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22562
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____22544;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____22545;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____22561
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
                                     uu____22492;
                                   FStar_Syntax_Syntax.ret_wp = uu____22508;
                                   FStar_Syntax_Syntax.bind_wp = uu____22509;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____22510;
                                   FStar_Syntax_Syntax.ite_wp = uu____22511;
                                   FStar_Syntax_Syntax.stronger = uu____22512;
                                   FStar_Syntax_Syntax.close_wp = uu____22513;
                                   FStar_Syntax_Syntax.assert_p = uu____22514;
                                   FStar_Syntax_Syntax.assume_p = uu____22515;
                                   FStar_Syntax_Syntax.null_wp = uu____22516;
                                   FStar_Syntax_Syntax.trivial = uu____22517;
                                   FStar_Syntax_Syntax.repr = uu____22518;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____22534;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____22535;
                                   FStar_Syntax_Syntax.actions = uu____22536;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____22579 =
                                     let uu____22580 =
                                       let uu____22589 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____22589
                                        in
                                     FStar_List.length uu____22580  in
                                   uu____22579 = (Prims.parse_int "1")  in
                                 let uu____22620 =
                                   let uu____22623 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____22623 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____22620;
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
                                             let uu____22645 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____22645
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____22647 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____22647
                                 then
                                   let reflect_lid =
                                     let uu____22651 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____22651
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
    let uu____22661 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____22661 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____22712 ->
              let uu____22713 =
                let uu____22714 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____22714
                 in
              Prims.strcat "\n  " uu____22713
          | uu____22715 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____22728  ->
               match uu____22728 with
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
          let uu____22746 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____22746
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____22748 =
          let uu____22759 = FStar_Syntax_Syntax.as_arg arg  in [uu____22759]
           in
        FStar_Syntax_Util.mk_app fv uu____22748

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22790 = desugar_decl_noattrs env d  in
      match uu____22790 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____22808 = mk_comment_attr d  in uu____22808 :: attrs1  in
          let uu____22809 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___292_22815 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___292_22815.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___292_22815.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___292_22815.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___292_22815.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___293_22817 = sigelt  in
                      let uu____22818 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____22824 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____22824) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___293_22817.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___293_22817.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___293_22817.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___293_22817.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____22818
                      })) sigelts
             in
          (env1, uu____22809)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22845 = desugar_decl_aux env d  in
      match uu____22845 with
      | (env1,ses) ->
          let uu____22856 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____22856)

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
      | FStar_Parser_AST.Fsdoc uu____22884 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____22892 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____22892, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____22929  ->
                 match uu____22929 with | (x,uu____22937) -> x) tcs
             in
          let uu____22942 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____22942 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____22964;
                    FStar_Parser_AST.prange = uu____22965;_},uu____22966)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____22975;
                    FStar_Parser_AST.prange = uu____22976;_},uu____22977)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____22992;
                         FStar_Parser_AST.prange = uu____22993;_},uu____22994);
                    FStar_Parser_AST.prange = uu____22995;_},uu____22996)::[]
                   -> false
               | (p,uu____23024)::[] ->
                   let uu____23033 = is_app_pattern p  in
                   Prims.op_Negation uu____23033
               | uu____23034 -> false)
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
            let uu____23107 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____23107 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____23119 =
                     let uu____23120 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____23120.FStar_Syntax_Syntax.n  in
                   match uu____23119 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____23130) ->
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
                         | uu____23163::uu____23164 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____23167 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___258_23182  ->
                                     match uu___258_23182 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____23185;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____23186;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____23187;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____23188;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____23189;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____23190;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____23191;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____23203;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____23204;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____23205;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____23206;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____23207;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____23208;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____23222 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____23253  ->
                                   match uu____23253 with
                                   | (uu____23266,(uu____23267,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____23222
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____23285 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____23285
                         then
                           let uu____23288 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___294_23302 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___295_23304 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___295_23304.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___295_23304.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___294_23302.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___294_23302.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___294_23302.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___294_23302.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___294_23302.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___294_23302.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____23288)
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
                   | uu____23331 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____23337 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____23356 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____23337 with
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
                       let uu___296_23392 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___296_23392.FStar_Parser_AST.prange)
                       }
                   | uu____23399 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___297_23406 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___297_23406.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___297_23406.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___297_23406.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____23442 id1 =
                   match uu____23442 with
                   | (env1,ses) ->
                       let main =
                         let uu____23463 =
                           let uu____23464 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____23464  in
                         FStar_Parser_AST.mk_term uu____23463
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
                       let uu____23514 = desugar_decl env1 id_decl  in
                       (match uu____23514 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____23532 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____23532 FStar_Util.set_elements
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
            let uu____23555 = close_fun env t  in
            desugar_term env uu____23555  in
          let quals1 =
            let uu____23559 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____23559
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____23565 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____23565;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____23573 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____23573 with
           | (t,uu____23587) ->
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
            let uu____23617 =
              let uu____23626 = FStar_Syntax_Syntax.null_binder t  in
              [uu____23626]  in
            let uu____23645 =
              let uu____23648 =
                let uu____23649 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____23649  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____23648
               in
            FStar_Syntax_Util.arrow uu____23617 uu____23645  in
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
            let uu____23710 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____23710 with
            | FStar_Pervasives_Native.None  ->
                let uu____23713 =
                  let uu____23718 =
                    let uu____23719 =
                      let uu____23720 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____23720 " not found"  in
                    Prims.strcat "Effect name " uu____23719  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____23718)  in
                FStar_Errors.raise_error uu____23713
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____23724 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____23742 =
                  let uu____23745 =
                    let uu____23746 = desugar_term env t  in
                    ([], uu____23746)  in
                  FStar_Pervasives_Native.Some uu____23745  in
                (uu____23742, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____23759 =
                  let uu____23762 =
                    let uu____23763 = desugar_term env wp  in
                    ([], uu____23763)  in
                  FStar_Pervasives_Native.Some uu____23762  in
                let uu____23770 =
                  let uu____23773 =
                    let uu____23774 = desugar_term env t  in
                    ([], uu____23774)  in
                  FStar_Pervasives_Native.Some uu____23773  in
                (uu____23759, uu____23770)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____23786 =
                  let uu____23789 =
                    let uu____23790 = desugar_term env t  in
                    ([], uu____23790)  in
                  FStar_Pervasives_Native.Some uu____23789  in
                (FStar_Pervasives_Native.None, uu____23786)
             in
          (match uu____23724 with
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
            let uu____23824 =
              let uu____23825 =
                let uu____23832 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____23832, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____23825  in
            {
              FStar_Syntax_Syntax.sigel = uu____23824;
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
      let uu____23858 =
        FStar_List.fold_left
          (fun uu____23878  ->
             fun d  ->
               match uu____23878 with
               | (env1,sigelts) ->
                   let uu____23898 = desugar_decl env1 d  in
                   (match uu____23898 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____23858 with
      | (env1,sigelts) ->
          let rec forward acc uu___260_23943 =
            match uu___260_23943 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____23957,FStar_Syntax_Syntax.Sig_let uu____23958) ->
                     let uu____23971 =
                       let uu____23974 =
                         let uu___298_23975 = se2  in
                         let uu____23976 =
                           let uu____23979 =
                             FStar_List.filter
                               (fun uu___259_23993  ->
                                  match uu___259_23993 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____23997;
                                           FStar_Syntax_Syntax.vars =
                                             uu____23998;_},uu____23999);
                                      FStar_Syntax_Syntax.pos = uu____24000;
                                      FStar_Syntax_Syntax.vars = uu____24001;_}
                                      when
                                      let uu____24028 =
                                        let uu____24029 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____24029
                                         in
                                      uu____24028 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____24030 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____23979
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___298_23975.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___298_23975.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___298_23975.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___298_23975.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____23976
                         }  in
                       uu____23974 :: se1 :: acc  in
                     forward uu____23971 sigelts1
                 | uu____24035 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____24043 = forward [] sigelts  in (env1, uu____24043)
  
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
          | (FStar_Pervasives_Native.None ,uu____24104) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____24108;
               FStar_Syntax_Syntax.exports = uu____24109;
               FStar_Syntax_Syntax.is_interface = uu____24110;_},FStar_Parser_AST.Module
             (current_lid,uu____24112)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____24120) ->
              let uu____24123 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____24123
           in
        let uu____24128 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____24164 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____24164, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____24181 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____24181, mname, decls, false)
           in
        match uu____24128 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____24211 = desugar_decls env2 decls  in
            (match uu____24211 with
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
          let uu____24273 =
            (FStar_Options.interactive ()) &&
              (let uu____24275 =
                 let uu____24276 =
                   let uu____24277 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____24277  in
                 FStar_Util.get_file_extension uu____24276  in
               FStar_List.mem uu____24275 ["fsti"; "fsi"])
             in
          if uu____24273 then as_interface m else m  in
        let uu____24281 = desugar_modul_common curmod env m1  in
        match uu____24281 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____24299 = FStar_Syntax_DsEnv.pop ()  in
              (uu____24299, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____24319 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____24319 with
      | (env1,modul,pop_when_done) ->
          let uu____24333 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____24333 with
           | (env2,modul1) ->
               ((let uu____24345 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____24345
                 then
                   let uu____24346 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____24346
                 else ());
                (let uu____24348 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____24348, modul1))))
  
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
        (fun uu____24395  ->
           let uu____24396 = desugar_modul env modul  in
           match uu____24396 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____24437  ->
           let uu____24438 = desugar_decls env decls  in
           match uu____24438 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____24492  ->
             let uu____24493 = desugar_partial_modul modul env a_modul  in
             match uu____24493 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____24591 ->
                  let t =
                    let uu____24601 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____24601  in
                  let uu____24614 =
                    let uu____24615 = FStar_Syntax_Subst.compress t  in
                    uu____24615.FStar_Syntax_Syntax.n  in
                  (match uu____24614 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____24627,uu____24628)
                       -> bs1
                   | uu____24653 -> failwith "Impossible")
               in
            let uu____24662 =
              let uu____24669 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____24669
                FStar_Syntax_Syntax.t_unit
               in
            match uu____24662 with
            | (binders,uu____24671,binders_opening) ->
                let erase_term t =
                  let uu____24679 =
                    let uu____24680 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____24680  in
                  FStar_Syntax_Subst.close binders uu____24679  in
                let erase_tscheme uu____24698 =
                  match uu____24698 with
                  | (us,t) ->
                      let t1 =
                        let uu____24718 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____24718 t  in
                      let uu____24721 =
                        let uu____24722 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____24722  in
                      ([], uu____24721)
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
                    | uu____24745 ->
                        let bs =
                          let uu____24755 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____24755  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____24795 =
                          let uu____24796 =
                            let uu____24799 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____24799  in
                          uu____24796.FStar_Syntax_Syntax.n  in
                        (match uu____24795 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____24801,uu____24802) -> bs1
                         | uu____24827 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____24834 =
                      let uu____24835 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____24835  in
                    FStar_Syntax_Subst.close binders uu____24834  in
                  let uu___299_24836 = action  in
                  let uu____24837 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____24838 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___299_24836.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___299_24836.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____24837;
                    FStar_Syntax_Syntax.action_typ = uu____24838
                  }  in
                let uu___300_24839 = ed  in
                let uu____24840 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____24841 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____24842 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____24843 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____24844 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____24845 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____24846 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____24847 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____24848 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____24849 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____24850 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____24851 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____24852 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____24853 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____24854 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____24855 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___300_24839.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___300_24839.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____24840;
                  FStar_Syntax_Syntax.signature = uu____24841;
                  FStar_Syntax_Syntax.ret_wp = uu____24842;
                  FStar_Syntax_Syntax.bind_wp = uu____24843;
                  FStar_Syntax_Syntax.if_then_else = uu____24844;
                  FStar_Syntax_Syntax.ite_wp = uu____24845;
                  FStar_Syntax_Syntax.stronger = uu____24846;
                  FStar_Syntax_Syntax.close_wp = uu____24847;
                  FStar_Syntax_Syntax.assert_p = uu____24848;
                  FStar_Syntax_Syntax.assume_p = uu____24849;
                  FStar_Syntax_Syntax.null_wp = uu____24850;
                  FStar_Syntax_Syntax.trivial = uu____24851;
                  FStar_Syntax_Syntax.repr = uu____24852;
                  FStar_Syntax_Syntax.return_repr = uu____24853;
                  FStar_Syntax_Syntax.bind_repr = uu____24854;
                  FStar_Syntax_Syntax.actions = uu____24855;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___300_24839.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___301_24871 = se  in
                  let uu____24872 =
                    let uu____24873 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____24873  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24872;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___301_24871.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___301_24871.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___301_24871.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___301_24871.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___302_24877 = se  in
                  let uu____24878 =
                    let uu____24879 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24879
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24878;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___302_24877.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___302_24877.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___302_24877.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___302_24877.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____24881 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____24882 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____24882 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____24894 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____24894
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____24896 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____24896)
  