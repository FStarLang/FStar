open Prims
type annotated_pat =
  (FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.bv *
    FStar_Syntax_Syntax.typ) Prims.list)
let (desugar_disjunctive_pattern :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list) Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.branch Prims.list)
  =
  fun annotated_pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu____173  ->
                match uu____173 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____282  ->
                             match uu____282 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____349 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____349 [] br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____385 =
                                     let uu____386 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____386]  in
                                   FStar_Syntax_Subst.close uu____385 branch1
                                    in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch2))
                                   FStar_Pervasives_Native.None
                                   br.FStar_Syntax_Syntax.pos) branch1 annots
                       in
                    FStar_Syntax_Util.branch (pat, when_opt, branch2)))
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___0_505  ->
        match uu___0_505 with
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
  fun uu___1_541  ->
    match uu___1_541 with
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
  fun uu___2_559  ->
    match uu___2_559 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____562 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____570 .
    FStar_Parser_AST.imp ->
      'Auu____570 ->
        ('Auu____570 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____596 .
    FStar_Parser_AST.imp ->
      'Auu____596 ->
        ('Auu____596 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____615 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____656 -> true
            | uu____667 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____691 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____701 =
      let uu____702 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____702  in
    FStar_Parser_AST.mk_term uu____701 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____723 =
      let uu____724 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____724  in
    FStar_Parser_AST.mk_term uu____723 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____754 =
        let uu____755 = unparen t  in uu____755.FStar_Parser_AST.tm  in
      match uu____754 with
      | FStar_Parser_AST.Name l ->
          let uu____768 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____768 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____787) ->
          let uu____814 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____814 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____833,uu____834) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____854,uu____855) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____878,t1) -> is_comp_type env t1
      | uu____894 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
type env_t = FStar_Syntax_DsEnv.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let (desugar_name' :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env_t ->
      Prims.bool ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun setpos  ->
    fun env  ->
      fun resolve  ->
        fun l  ->
          let tm_attrs_opt =
            if resolve
            then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes env l
            else
              FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve
                env l
             in
          match tm_attrs_opt with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (tm,attrs) ->
              let warn_if_deprecated attrs1 =
                FStar_List.iter
                  (fun a  ->
                     match a.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu____1110;
                            FStar_Syntax_Syntax.vars = uu____1111;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____1162 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____1162 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____1182 =
                               let uu____1183 =
                                 let uu____1194 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____1194  in
                               uu____1183.FStar_Syntax_Syntax.n  in
                             match uu____1182 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____1229))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____1236 -> msg
                           else msg  in
                         let uu____1239 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____1239
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____1251 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____1251 " is deprecated"  in
                         let uu____1254 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____1254
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____1256 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____1284 .
    'Auu____1284 ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        env_t -> Prims.bool -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            FStar_Syntax_DsEnv.fail_or env (desugar_name' setpos env resolve)
              l
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____1373 =
          let uu____1378 =
            let uu____1383 =
              let uu____1389 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____1389, r)  in
            FStar_Ident.mk_ident uu____1383  in
          [uu____1378]  in
        FStar_All.pipe_right uu____1373 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____1415 .
    env_t ->
      Prims.int ->
        'Auu____1415 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____1473 =
              let uu____1482 =
                let uu____1489 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____1489 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____1482 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____1473  in
          let fallback uu____1520 =
            let uu____1521 = FStar_Ident.text_of_id op  in
            match uu____1521 with
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
                let uu____1546 = FStar_Options.ml_ish ()  in
                if uu____1546
                then
                  r FStar_Parser_Const.list_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
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
            | uu____1575 -> FStar_Pervasives_Native.None  in
          let uu____1581 =
            let uu____1588 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___205_1606 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___205_1606.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___205_1606.FStar_Syntax_Syntax.vars)
                 }) env true uu____1588
             in
          match uu____1581 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____1635 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____1660 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____1660
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____1744 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____1756 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____1756 with | (env1,uu____1775) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____1794,term) ->
          let uu____1806 = free_type_vars env term  in (env, uu____1806)
      | FStar_Parser_AST.TAnnotated (id1,uu____1816) ->
          let uu____1827 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____1827 with | (env1,uu____1846) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____1867 = free_type_vars env t  in (env, uu____1867)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____1881 =
        let uu____1882 = unparen t  in uu____1882.FStar_Parser_AST.tm  in
      match uu____1881 with
      | FStar_Parser_AST.Labeled uu____1893 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____1913 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____1913 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____1932 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____1943 -> []
      | FStar_Parser_AST.Uvar uu____1946 -> []
      | FStar_Parser_AST.Var uu____1951 -> []
      | FStar_Parser_AST.Projector uu____1958 -> []
      | FStar_Parser_AST.Discrim uu____1971 -> []
      | FStar_Parser_AST.Name uu____1978 -> []
      | FStar_Parser_AST.Requires (t1,uu____1986) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____2000) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____2013,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____2100,ts) ->
          FStar_List.collect
            (fun uu____2140  ->
               match uu____2140 with
               | (t1,uu____2153) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____2160,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____2183) ->
          let uu____2196 = free_type_vars env t1  in
          let uu____2201 = free_type_vars env t2  in
          FStar_List.append uu____2196 uu____2201
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____2224 = free_type_vars_b env b  in
          (match uu____2224 with
           | (env1,f) ->
               let uu____2247 = free_type_vars env1 t1  in
               FStar_List.append f uu____2247)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____2288 =
            FStar_List.fold_left
              (fun uu____2323  ->
                 fun bt  ->
                   match uu____2323 with
                   | (env1,free) ->
                       let uu____2362 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____2402 = free_type_vars env1 body  in
                             (env1, uu____2402)
                          in
                       (match uu____2362 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____2288 with
           | (env1,free) ->
               let uu____2455 = free_type_vars env1 body  in
               FStar_List.append free uu____2455)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____2482 =
            FStar_List.fold_left
              (fun uu____2510  ->
                 fun binder  ->
                   match uu____2510 with
                   | (env1,free) ->
                       let uu____2542 = free_type_vars_b env1 binder  in
                       (match uu____2542 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____2482 with
           | (env1,free) ->
               let uu____2595 = free_type_vars env1 body  in
               FStar_List.append free uu____2595)
      | FStar_Parser_AST.Project (t1,uu____2603) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____2650 = free_type_vars env rel  in
          let uu____2655 =
            let uu____2660 = free_type_vars env init1  in
            let uu____2665 =
              FStar_List.collect
                (fun uu____2679  ->
                   match uu____2679 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____2706 = free_type_vars env rel1  in
                       let uu____2711 =
                         let uu____2716 = free_type_vars env just  in
                         let uu____2721 = free_type_vars env next  in
                         FStar_List.append uu____2716 uu____2721  in
                       FStar_List.append uu____2706 uu____2711) steps
               in
            FStar_List.append uu____2660 uu____2665  in
          FStar_List.append uu____2650 uu____2655
      | FStar_Parser_AST.Abs uu____2734 -> []
      | FStar_Parser_AST.Let uu____2748 -> []
      | FStar_Parser_AST.LetOpen uu____2782 -> []
      | FStar_Parser_AST.If uu____2796 -> []
      | FStar_Parser_AST.QForall uu____2814 -> []
      | FStar_Parser_AST.QExists uu____2847 -> []
      | FStar_Parser_AST.Record uu____2880 -> []
      | FStar_Parser_AST.Match uu____2905 -> []
      | FStar_Parser_AST.TryWith uu____2933 -> []
      | FStar_Parser_AST.Bind uu____2961 -> []
      | FStar_Parser_AST.Quote uu____2978 -> []
      | FStar_Parser_AST.VQuote uu____2988 -> []
      | FStar_Parser_AST.Antiquote uu____2994 -> []
      | FStar_Parser_AST.Seq uu____3000 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____3092 =
        let uu____3093 = unparen t1  in uu____3093.FStar_Parser_AST.tm  in
      match uu____3092 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____3188 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____3233 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____3233  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____3284 =
                     let uu____3285 =
                       let uu____3295 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____3295)  in
                     FStar_Parser_AST.TAnnotated uu____3285  in
                   FStar_Parser_AST.mk_binder uu____3284
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
        let uu____3348 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____3348  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____3399 =
                     let uu____3400 =
                       let uu____3410 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____3410)  in
                     FStar_Parser_AST.TAnnotated uu____3400  in
                   FStar_Parser_AST.mk_binder uu____3399
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____3429 =
             let uu____3430 = unparen t  in uu____3430.FStar_Parser_AST.tm
              in
           match uu____3429 with
           | FStar_Parser_AST.Product uu____3440 -> t
           | uu____3454 ->
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
      (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term))
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____3556 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____3578 -> true
    | FStar_Parser_AST.PatTvar (uu____3582,uu____3583) -> true
    | FStar_Parser_AST.PatVar (uu____3593,uu____3594) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____3605) -> is_var_pattern p1
    | uu____3634 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____3649) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____3678;
           FStar_Parser_AST.prange = uu____3679;_},uu____3680)
        -> true
    | uu____3700 -> false
  
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern
                 (FStar_Parser_AST.PatWild FStar_Pervasives_Native.None)
                 p.FStar_Parser_AST.prange),
               (unit_ty, FStar_Pervasives_Native.None)))
          p.FStar_Parser_AST.prange
    | uu____3745 -> p
  
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term *
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____3866 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____3866 with
             | (name,args,uu____3937) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____4035);
               FStar_Parser_AST.prange = uu____4036;_},args)
            when is_top_level1 ->
            let uu____4056 =
              let uu____4067 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____4067  in
            (uu____4056, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____4123);
               FStar_Parser_AST.prange = uu____4124;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____4190 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  Prims.bool ->
    FStar_Ident.ident FStar_Util.set ->
      FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst  ->
    fun acc  ->
      fun p  ->
        let gather_pattern_bound_vars_from_list =
          FStar_List.fold_left
            (gather_pattern_bound_vars_maybe_top fail_on_patconst) acc
           in
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatWild uu____4283 -> acc
        | FStar_Parser_AST.PatName uu____4286 -> acc
        | FStar_Parser_AST.PatOp uu____4291 -> acc
        | FStar_Parser_AST.PatConst uu____4294 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____4325) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____4337) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____4354) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____4383 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____4383
        | FStar_Parser_AST.PatAscribed (pat,uu____4407) ->
            gather_pattern_bound_vars_maybe_top fail_on_patconst acc pat
  
let (gather_pattern_bound_vars :
  Prims.bool -> FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst  ->
    fun p  ->
      let acc =
        FStar_Util.new_set
          (fun id1  ->
             fun id2  ->
               if id1.FStar_Ident.idText = id2.FStar_Ident.idText
               then (Prims.parse_int "0")
               else (Prims.parse_int "1"))
         in
      gather_pattern_bound_vars_maybe_top fail_on_patconst acc p
  
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____4543 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____4611 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_4700  ->
    match uu___3_4700 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____4727 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____4806  ->
    match uu____4806 with
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
      let uu____4988 =
        let uu____5013 =
          let uu____5024 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____5024  in
        let uu____5031 =
          let uu____5046 =
            let uu____5059 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____5059)  in
          [uu____5046]  in
        (uu____5013, uu____5031)  in
      FStar_Syntax_Syntax.Tm_app uu____4988  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____5140 =
        let uu____5165 =
          let uu____5176 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____5176  in
        let uu____5183 =
          let uu____5198 =
            let uu____5211 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____5211)  in
          [uu____5198]  in
        (uu____5165, uu____5183)  in
      FStar_Syntax_Syntax.Tm_app uu____5140  in
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
          let uu____5314 =
            let uu____5339 =
              let uu____5350 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____5350  in
            let uu____5357 =
              let uu____5372 =
                let uu____5385 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____5385)  in
              let uu____5397 =
                let uu____5412 =
                  let uu____5425 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____5425)  in
                [uu____5412]  in
              uu____5372 :: uu____5397  in
            (uu____5339, uu____5357)  in
          FStar_Syntax_Syntax.Tm_app uu____5314  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____5533 =
        let uu____5555 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____5585  ->
               match uu____5585 with
               | ({ FStar_Syntax_Syntax.ppname = uu____5605;
                    FStar_Syntax_Syntax.index = uu____5606;
                    FStar_Syntax_Syntax.sort = t;_},uu____5608)
                   ->
                   let uu____5627 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____5627) uu____5555
         in
      FStar_All.pipe_right bs uu____5533  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____5663 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____5702 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____5769 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____5817,uu____5818,bs,t,uu____5821,uu____5822)
                            ->
                            let uu____5863 = bs_univnames bs  in
                            let uu____5868 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____5863 uu____5868
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____5875,uu____5876,t,uu____5878,uu____5879,uu____5880)
                            -> FStar_Syntax_Free.univnames t
                        | uu____5919 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____5769 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___587_5936 = s  in
        let uu____5947 =
          let uu____5948 =
            let uu____5966 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____6019,bs,t,lids1,lids2) ->
                          let uu___598_6064 = se  in
                          let uu____6075 =
                            let uu____6076 =
                              let uu____6109 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____6110 =
                                let uu____6119 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____6119 t  in
                              (lid, uvs, uu____6109, uu____6110, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____6076
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____6075;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___598_6064.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___598_6064.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___598_6064.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___598_6064.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____6154,t,tlid,n1,lids1) ->
                          let uu___608_6197 = se  in
                          let uu____6208 =
                            let uu____6209 =
                              let uu____6241 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____6241, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____6209  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____6208;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___608_6197.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___608_6197.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___608_6197.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___608_6197.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____6269 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____5966, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____5948  in
        {
          FStar_Syntax_Syntax.sigel = uu____5947;
          FStar_Syntax_Syntax.sigrng =
            (uu___587_5936.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___587_5936.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___587_5936.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___587_5936.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6290,t) ->
        let uvs =
          let uu____6309 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____6309 FStar_Util.set_elements  in
        let uu___617_6320 = s  in
        let uu____6331 =
          let uu____6332 =
            let uu____6347 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____6347)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____6332  in
        {
          FStar_Syntax_Syntax.sigel = uu____6331;
          FStar_Syntax_Syntax.sigrng =
            (uu___617_6320.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___617_6320.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___617_6320.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___617_6320.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____6427 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____6432 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____6443) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____6514,(FStar_Util.Inl t,uu____6516),uu____6517)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____6620,(FStar_Util.Inr c,uu____6622),uu____6623)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____6726 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____6729,(FStar_Util.Inl t,uu____6731),uu____6732) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____6835,(FStar_Util.Inr c,uu____6837),uu____6838) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____6941 -> empty_set  in
          FStar_Util.set_union uu____6427 uu____6432  in
        let all_lb_univs =
          let uu____6949 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____6994 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____6994) empty_set)
             in
          FStar_All.pipe_right uu____6949 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___672_7014 = s  in
        let uu____7025 =
          let uu____7026 =
            let uu____7037 =
              let uu____7038 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___675_7092 = lb  in
                        let uu____7107 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____7118 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___675_7092.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____7107;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___675_7092.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7118;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___675_7092.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___675_7092.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____7038)  in
            (uu____7037, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____7026  in
        {
          FStar_Syntax_Syntax.sigel = uu____7025;
          FStar_Syntax_Syntax.sigrng =
            (uu___672_7014.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___672_7014.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___672_7014.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___672_7014.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____7146,fml) ->
        let uvs =
          let uu____7165 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____7165 FStar_Util.set_elements  in
        let uu___683_7176 = s  in
        let uu____7187 =
          let uu____7188 =
            let uu____7203 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____7203)  in
          FStar_Syntax_Syntax.Sig_assume uu____7188  in
        {
          FStar_Syntax_Syntax.sigel = uu____7187;
          FStar_Syntax_Syntax.sigrng =
            (uu___683_7176.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___683_7176.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___683_7176.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___683_7176.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____7221,bs,c,flags) ->
        let uvs =
          let uu____7246 =
            let uu____7251 = bs_univnames bs  in
            let uu____7256 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____7251 uu____7256  in
          FStar_All.pipe_right uu____7246 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___694_7272 = s  in
        let uu____7283 =
          let uu____7284 =
            let uu____7305 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____7306 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____7305, uu____7306, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____7284  in
        {
          FStar_Syntax_Syntax.sigel = uu____7283;
          FStar_Syntax_Syntax.sigrng =
            (uu___694_7272.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___694_7272.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___694_7272.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___694_7272.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____7325 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_7333  ->
    match uu___4_7333 with
    | "lift1" -> true
    | "lift2" -> true
    | "pure" -> true
    | "app" -> true
    | "push" -> true
    | "wp_if_then_else" -> true
    | "wp_assert" -> true
    | "wp_assume" -> true
    | "wp_close" -> true
    | "stronger" -> true
    | "ite_wp" -> true
    | "null_wp" -> true
    | "wp_trivial" -> true
    | "ctx" -> true
    | "gctx" -> true
    | "lift_from_pure" -> true
    | "return_wp" -> true
    | "return_elab" -> true
    | "bind_wp" -> true
    | "bind_elab" -> true
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____7384 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____7405 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____7405)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____7437 =
      let uu____7438 = unparen t  in uu____7438.FStar_Parser_AST.tm  in
    match uu____7437 with
    | FStar_Parser_AST.Wild  ->
        let uu____7450 =
          let uu____7451 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____7451  in
        FStar_Util.Inr uu____7450
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____7468)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < (Prims.parse_int "0")
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.op_Hat
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
             let uu____7581 = sum_to_universe u n1  in
             FStar_Util.Inr uu____7581
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____7598 = sum_to_universe u n1  in
             FStar_Util.Inr uu____7598
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____7614 =
               let uu____7620 =
                 let uu____7622 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____7622
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____7620)
                in
             FStar_Errors.raise_error uu____7614 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____7631 ->
        let rec aux t1 univargs =
          let uu____7680 =
            let uu____7681 = unparen t1  in uu____7681.FStar_Parser_AST.tm
             in
          match uu____7680 with
          | FStar_Parser_AST.App (t2,targ,uu____7695) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_7738  ->
                     match uu___5_7738 with
                     | FStar_Util.Inr uu____7745 -> true
                     | uu____7748 -> false) univargs
              then
                let uu____7756 =
                  let uu____7757 =
                    FStar_List.map
                      (fun uu___6_7767  ->
                         match uu___6_7767 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____7757  in
                FStar_Util.Inr uu____7756
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_7793  ->
                        match uu___7_7793 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____7803 -> failwith "impossible")
                     univargs
                    in
                 let uu____7807 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____7807)
          | uu____7823 ->
              let uu____7824 =
                let uu____7830 =
                  let uu____7832 =
                    let uu____7834 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____7834 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____7832  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____7830)  in
              FStar_Errors.raise_error uu____7824 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____7849 ->
        let uu____7850 =
          let uu____7856 =
            let uu____7858 =
              let uu____7860 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____7860 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____7858  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____7856)  in
        FStar_Errors.raise_error uu____7850 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____7916;_});
            FStar_Syntax_Syntax.pos = uu____7917;
            FStar_Syntax_Syntax.vars = uu____7918;_})::uu____7919
        ->
        let uu____8005 =
          let uu____8011 =
            let uu____8013 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____8013
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____8011)  in
        FStar_Errors.raise_error uu____8005 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____8019 ->
        let uu____8074 =
          let uu____8080 =
            let uu____8082 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____8082
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____8080)  in
        FStar_Errors.raise_error uu____8074 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____8095 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____8095) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____8141 = FStar_List.hd fields  in
        match uu____8141 with
        | (f,uu____8169) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____8223 =
                match uu____8223 with
                | (f',uu____8233) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____8243 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____8243
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
              (let uu____8253 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____8253);
              (match () with | () -> record)))
  
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun env  ->
    fun p  ->
      let check_linear_pattern_variables pats r =
        let rec pat_vars p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_dot_term uu____8762 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____8778 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____8784 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____8796,pats1) ->
              let aux out uu____8862 =
                match uu____8862 with
                | (p2,uu____8885) ->
                    let intersection =
                      let uu____8906 = pat_vars p2  in
                      FStar_Util.set_intersect uu____8906 out  in
                    let uu____8919 = FStar_Util.set_is_empty intersection  in
                    if uu____8919
                    then
                      let uu____8934 = pat_vars p2  in
                      FStar_Util.set_union out uu____8934
                    else
                      (let duplicate_bv =
                         let uu____8960 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____8960  in
                       let uu____8978 =
                         let uu____8984 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____8984)
                          in
                       FStar_Errors.raise_error uu____8978 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____9033 = pat_vars p1  in
            FStar_All.pipe_right uu____9033 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____9088 =
                let uu____9090 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____9090  in
              if uu____9088
              then ()
              else
                (let nonlinear_vars =
                   let uu____9114 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____9114  in
                 let first_nonlinear_var =
                   let uu____9138 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____9138  in
                 let uu____9156 =
                   let uu____9162 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____9162)  in
                 FStar_Errors.raise_error uu____9156 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____9202 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____9202 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____9264 ->
            let uu____9272 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____9272 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____9513 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____9550 =
              let uu____9555 =
                let uu____9556 =
                  let uu____9565 =
                    let uu____9570 =
                      let uu____9576 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____9576, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____9570  in
                  (uu____9565, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____9556  in
              {
                FStar_Parser_AST.pat = uu____9555;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____9550
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____9623 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____9632 = aux loc env1 p2  in
              match uu____9632 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___932_9788 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___934_9796 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___934_9796.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___934_9796.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___932_9788.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___938_9813 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___940_9821 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___940_9821.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___940_9821.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___938_9813.FStar_Syntax_Syntax.p)
                        }
                    | uu____9832 when top -> p4
                    | uu____9833 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____9841 =
                    match binder with
                    | LetBinder uu____9880 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____9944 = close_fun env1 t  in
                          desugar_term env1 uu____9944  in
                        let x1 =
                          let uu___951_9962 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___951_9962.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___951_9962.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____9841 with
                   | (annots',binder1) ->
                       (loc1, env', binder1, p3,
                         (FStar_List.append annots' annots), imp))))
        | FStar_Parser_AST.PatWild aq ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____10136 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____10136, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____10183 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____10183, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____10234 = resolvex loc env1 x  in
            (match uu____10234 with
             | (loc1,env2,xbv) ->
                 let uu____10287 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____10287, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____10337 = resolvex loc env1 x  in
            (match uu____10337 with
             | (loc1,env2,xbv) ->
                 let uu____10390 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____10390, [], imp))
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
            let uu____10451 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____10451, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____10513;_},args)
            ->
            let uu____10529 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____10616  ->
                     match uu____10616 with
                     | (loc1,env2,annots,args1) ->
                         let uu____10744 = aux loc1 env2 arg  in
                         (match uu____10744 with
                          | (loc2,env3,uu____10815,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____10529 with
             | (loc1,env2,annots,args1) ->
                 let l1 =
                   FStar_Syntax_DsEnv.fail_or env2
                     (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____11074 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____11074, annots, false))
        | FStar_Parser_AST.PatApp uu____11112 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____11158 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____11235  ->
                     match uu____11235 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____11343 = aux loc1 env2 pat  in
                         (match uu____11343 with
                          | (loc2,env3,uu____11409,pat1,ans,uu____11412) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____11158 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____11617 =
                     let uu____11623 =
                       let uu____11633 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____11633  in
                     let uu____11634 =
                       let uu____11635 =
                         let uu____11655 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____11655, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____11635  in
                     FStar_All.pipe_left uu____11623 uu____11634  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____11713 =
                            let uu____11714 =
                              let uu____11734 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____11734, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____11714  in
                          FStar_All.pipe_left (pos_r r) uu____11713) pats1
                     uu____11617
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                   annots, false))
        | FStar_Parser_AST.PatTuple (args,dep1) ->
            let uu____11850 =
              FStar_List.fold_left
                (fun uu____11936  ->
                   fun p2  ->
                     match uu____11936 with
                     | (loc1,env2,annots,pats) ->
                         let uu____12065 = aux loc1 env2 p2  in
                         (match uu____12065 with
                          | (loc2,env3,uu____12136,pat,ans,uu____12139) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____11850 with
             | (loc1,env2,annots,args1) ->
                 let args2 = FStar_List.rev args1  in
                 let l =
                   if dep1
                   then
                     FStar_Parser_Const.mk_dtuple_data_lid
                       (FStar_List.length args2) p1.FStar_Parser_AST.prange
                   else
                     FStar_Parser_Const.mk_tuple_data_lid
                       (FStar_List.length args2) p1.FStar_Parser_AST.prange
                    in
                 let constr =
                   FStar_Syntax_DsEnv.fail_or env2
                     (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                    in
                 let l1 =
                   match constr.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                   | uu____12461 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____12477 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____12477, annots, false))
        | FStar_Parser_AST.PatRecord [] ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatRecord fields ->
            let record = check_fields env1 fields p1.FStar_Parser_AST.prange
               in
            let fields1 =
              FStar_All.pipe_right fields
                (FStar_List.map
                   (fun uu____12645  ->
                      match uu____12645 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____12719  ->
                      match uu____12719 with
                      | (f,uu____12733) ->
                          let uu____12746 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____12788  ->
                                    match uu____12788 with
                                    | (g,uu____12799) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____12746 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____12819,p2) ->
                               p2)))
               in
            let app =
              let uu____12842 =
                let uu____12843 =
                  let uu____12854 =
                    let uu____12859 =
                      let uu____12860 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____12860  in
                    FStar_Parser_AST.mk_pattern uu____12859
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____12854, args)  in
                FStar_Parser_AST.PatApp uu____12843  in
              FStar_Parser_AST.mk_pattern uu____12842
                p1.FStar_Parser_AST.prange
               in
            let uu____12881 = aux loc env1 app  in
            (match uu____12881 with
             | (env2,e,b,p2,annots,uu____12948) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____13024 =
                         let uu____13025 =
                           let uu____13045 =
                             let uu___1099_13052 = fv  in
                             let uu____13059 =
                               let uu____13062 =
                                 let uu____13063 =
                                   let uu____13076 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____13076)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____13063
                                  in
                               FStar_Pervasives_Native.Some uu____13062  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1099_13052.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1099_13052.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____13059
                             }  in
                           (uu____13045, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____13025  in
                       FStar_All.pipe_left pos uu____13024
                   | uu____13138 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____13284 = aux' true loc env1 p2  in
            (match uu____13284 with
             | (loc1,env2,var,p3,ans,uu____13346) ->
                 let uu____13379 =
                   FStar_List.fold_left
                     (fun uu____13448  ->
                        fun p4  ->
                          match uu____13448 with
                          | (loc2,env3,ps1) ->
                              let uu____13551 = aux' true loc2 env3 p4  in
                              (match uu____13551 with
                               | (loc3,env4,uu____13610,p5,ans1,uu____13613)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____13379 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____13909 ->
            let uu____13910 = aux' true loc env1 p1  in
            (match uu____13910 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____14079 = aux_maybe_or env p  in
      match uu____14079 with
      | (env1,b,pats) ->
          ((let uu____14161 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____14161
              p.FStar_Parser_AST.prange);
           (env1, b, pats))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top  ->
    fun env  ->
      fun p  ->
        let mklet x ty tacopt =
          let uu____14280 =
            let uu____14281 =
              let uu____14304 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____14304, (ty, tacopt))  in
            LetBinder uu____14281  in
          (env, uu____14280, [])  in
        let op_to_ident x =
          let uu____14355 =
            let uu____14361 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____14361, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____14355  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____14385 = op_to_ident x  in
              mklet uu____14385 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____14395) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____14409;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____14458 = op_to_ident x  in
              let uu____14463 = desugar_term env t  in
              mklet uu____14458 uu____14463 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____14473);
                 FStar_Parser_AST.prange = uu____14474;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____14529 = desugar_term env t  in
              mklet x uu____14529 tacopt1
          | uu____14538 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____14551 = desugar_data_pat env p  in
           match uu____14551 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____14580;
                      FStar_Syntax_Syntax.p = uu____14581;_},uu____14582)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____14618;
                      FStar_Syntax_Syntax.p = uu____14619;_},uu____14620)::[]
                     -> []
                 | uu____14656 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____14666  ->
    fun env  ->
      fun pat  ->
        let uu____14672 = desugar_data_pat env pat  in
        match uu____14672 with | (env1,uu____14688,pat1) -> (env1, pat1)

and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and (desugar_term_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
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
      let uu____14726 = desugar_term_aq env e  in
      match uu____14726 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_typ_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
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
      let uu____14775 = desugar_typ_aq env e  in
      match uu____14775 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____14801  ->
        fun range  ->
          match uu____14801 with
          | (signedness,width) ->
              let tnm =
                Prims.op_Hat "FStar."
                  (Prims.op_Hat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.op_Hat "Int"
                        (match width with
                         | FStar_Const.Int8  -> "8"
                         | FStar_Const.Int16  -> "16"
                         | FStar_Const.Int32  -> "32"
                         | FStar_Const.Int64  -> "64")))
                 in
              ((let uu____14827 =
                  let uu____14829 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____14829  in
                if uu____14827
                then
                  let uu____14832 =
                    let uu____14838 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____14838)  in
                  FStar_Errors.log_issue range uu____14832
                else ());
               (let private_intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat ".__"
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat "."
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let lid =
                  let uu____14867 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____14867 range  in
                let lid1 =
                  let uu____14879 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____14879 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____14920 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____14920 range  in
                           let private_fv =
                             let uu____14928 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____14928 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1269_14929 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1269_14929.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1269_14929.FStar_Syntax_Syntax.vars)
                           }
                       | uu____14938 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____14950 =
                        let uu____14956 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____14956)
                         in
                      FStar_Errors.raise_error uu____14950 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____14988 =
                  let uu____14995 =
                    let uu____14996 =
                      let uu____15021 =
                        let uu____15036 =
                          let uu____15049 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____15049)  in
                        [uu____15036]  in
                      (lid1, uu____15021)  in
                    FStar_Syntax_Syntax.Tm_app uu____14996  in
                  FStar_Syntax_Syntax.mk uu____14995  in
                uu____14988 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____15126 =
          let uu____15127 = unparen t  in uu____15127.FStar_Parser_AST.tm  in
        match uu____15126 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____15134; FStar_Ident.ident = uu____15135;
              FStar_Ident.nsstr = uu____15136; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____15145 ->
            let uu____15146 =
              let uu____15152 =
                let uu____15154 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____15154  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____15152)  in
            FStar_Errors.raise_error uu____15146 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes

and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
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
          let uu___1296_15329 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1296_15329.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1296_15329.FStar_Syntax_Syntax.vars)
          }  in
        let uu____15340 =
          let uu____15341 = unparen top  in uu____15341.FStar_Parser_AST.tm
           in
        match uu____15340 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____15360 ->
            let uu____15372 = desugar_formula env top  in
            (uu____15372, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____15399 = desugar_formula env t  in (uu____15399, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____15426 = desugar_formula env t  in (uu____15426, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____15472 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____15472, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____15486 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____15486, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____15521 =
                let uu____15522 =
                  let uu____15534 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____15534, args)  in
                FStar_Parser_AST.Op uu____15522  in
              FStar_Parser_AST.mk_term uu____15521 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15548 =
              let uu____15555 =
                let uu____15556 =
                  let uu____15568 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____15568, [e])  in
                FStar_Parser_AST.Op uu____15556  in
              FStar_Parser_AST.mk_term uu____15555 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____15548
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____15617 = FStar_Ident.text_of_id op_star  in
             uu____15617 = "*") &&
              (let uu____15622 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____15622 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____15663;_},t1::t2::[])
                  when
                  let uu____15689 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____15689 FStar_Option.isNone ->
                  let uu____15708 = flatten1 t1  in
                  FStar_List.append uu____15708 [t2]
              | uu____15723 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1344_15743 = top  in
              let uu____15750 =
                let uu____15751 =
                  let uu____15772 =
                    FStar_List.map (fun _15807  -> FStar_Util.Inr _15807)
                      terms
                     in
                  (uu____15772, rhs)  in
                FStar_Parser_AST.Sum uu____15751  in
              {
                FStar_Parser_AST.tm = uu____15750;
                FStar_Parser_AST.range =
                  (uu___1344_15743.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1344_15743.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____15827 =
              let uu____15836 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____15836  in
            (uu____15827, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____15868 =
              let uu____15874 =
                let uu____15876 =
                  let uu____15878 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____15878 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____15876  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____15874)
               in
            FStar_Errors.raise_error uu____15868 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____15907 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____15907 with
             | FStar_Pervasives_Native.None  ->
                 let uu____15929 =
                   let uu____15935 =
                     let uu____15937 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____15937
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____15935)
                    in
                 FStar_Errors.raise_error uu____15929
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____15971 =
                     let uu____16009 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____16110 = desugar_term_aq env t  in
                               match uu____16110 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____16009 FStar_List.unzip  in
                   (match uu____15971 with
                    | (args1,aqs) ->
                        let uu____16336 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____16336, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____16377)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____16417 =
              let uu___1373_16424 = top  in
              let uu____16431 =
                let uu____16432 =
                  let uu____16445 =
                    let uu___1375_16452 = top  in
                    let uu____16459 =
                      let uu____16460 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____16460  in
                    {
                      FStar_Parser_AST.tm = uu____16459;
                      FStar_Parser_AST.range =
                        (uu___1375_16452.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1375_16452.FStar_Parser_AST.level)
                    }  in
                  (uu____16445, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____16432  in
              {
                FStar_Parser_AST.tm = uu____16431;
                FStar_Parser_AST.range =
                  (uu___1373_16424.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1373_16424.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____16417
        | FStar_Parser_AST.Construct (n1,(a,uu____16482)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____16525 =
                let uu___1385_16532 = top  in
                let uu____16539 =
                  let uu____16540 =
                    let uu____16553 =
                      let uu___1387_16560 = top  in
                      let uu____16567 =
                        let uu____16568 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____16568  in
                      {
                        FStar_Parser_AST.tm = uu____16567;
                        FStar_Parser_AST.range =
                          (uu___1387_16560.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1387_16560.FStar_Parser_AST.level)
                      }  in
                    (uu____16553, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____16540  in
                {
                  FStar_Parser_AST.tm = uu____16539;
                  FStar_Parser_AST.range =
                    (uu___1385_16532.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1385_16532.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____16525))
        | FStar_Parser_AST.Construct (n1,(a,uu____16590)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____16630 =
              let uu___1396_16637 = top  in
              let uu____16644 =
                let uu____16645 =
                  let uu____16658 =
                    let uu___1398_16665 = top  in
                    let uu____16672 =
                      let uu____16673 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____16673  in
                    {
                      FStar_Parser_AST.tm = uu____16672;
                      FStar_Parser_AST.range =
                        (uu___1398_16665.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1398_16665.FStar_Parser_AST.level)
                    }  in
                  (uu____16658, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____16645  in
              {
                FStar_Parser_AST.tm = uu____16644;
                FStar_Parser_AST.range =
                  (uu___1396_16637.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1396_16637.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____16630
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____16693; FStar_Ident.ident = uu____16694;
              FStar_Ident.nsstr = uu____16695; FStar_Ident.str = "Type0";_}
            ->
            let uu____16704 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____16704, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____16717; FStar_Ident.ident = uu____16718;
              FStar_Ident.nsstr = uu____16719; FStar_Ident.str = "Type";_}
            ->
            let uu____16728 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____16728, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____16741; FStar_Ident.ident = uu____16742;
               FStar_Ident.nsstr = uu____16743; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____16786 =
              let uu____16795 =
                let uu____16796 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____16796  in
              mk1 uu____16795  in
            (uu____16786, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____16801; FStar_Ident.ident = uu____16802;
              FStar_Ident.nsstr = uu____16803; FStar_Ident.str = "Effect";_}
            ->
            let uu____16812 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____16812, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____16825; FStar_Ident.ident = uu____16826;
              FStar_Ident.nsstr = uu____16827; FStar_Ident.str = "True";_}
            ->
            let uu____16836 =
              let uu____16845 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____16845
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____16836, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____16858; FStar_Ident.ident = uu____16859;
              FStar_Ident.nsstr = uu____16860; FStar_Ident.str = "False";_}
            ->
            let uu____16869 =
              let uu____16878 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____16878
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____16869, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____16893;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____16906 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____16906 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____16987 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____16987, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____17021 =
                    let uu____17023 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____17023 txt
                     in
                  failwith uu____17021))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____17040 = desugar_name mk1 setpos env true l  in
              (uu____17040, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____17069 = desugar_name mk1 setpos env true l  in
              (uu____17069, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____17119 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____17119 with
                | FStar_Pervasives_Native.Some uu____17136 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____17161 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____17161 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____17203 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____17248 =
                    let uu____17257 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____17257  in
                  (uu____17248, noaqs)
              | uu____17279 ->
                  let uu____17291 =
                    let uu____17297 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____17297)  in
                  FStar_Errors.raise_error uu____17291
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____17315 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____17315 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17332 =
                    let uu____17338 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____17338)
                     in
                  FStar_Errors.raise_error uu____17332
                    top.FStar_Parser_AST.range
              | uu____17350 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____17365 = desugar_name mk1 setpos env true lid'  in
                  (uu____17365, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____17417 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____17417 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____17468 ->
                       let uu____17478 =
                         FStar_Util.take
                           (fun uu____17511  ->
                              match uu____17511 with
                              | (uu____17520,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____17478 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____17596 =
                              let uu____17634 =
                                FStar_List.map
                                  (fun uu____17697  ->
                                     match uu____17697 with
                                     | (t,imp) ->
                                         let uu____17727 =
                                           desugar_term_aq env t  in
                                         (match uu____17727 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____17634
                                FStar_List.unzip
                               in
                            (match uu____17596 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____17979 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____17979, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____18021 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____18021 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____18040 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_18107  ->
                 match uu___8_18107 with
                 | FStar_Util.Inr uu____18120 -> true
                 | uu____18132 -> false) binders
            ->
            let terms =
              let uu____18151 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_18191  ->
                        match uu___9_18191 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____18217 -> failwith "Impossible"))
                 in
              FStar_List.append uu____18151 [t]  in
            let uu____18242 =
              let uu____18280 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____18372 = desugar_typ_aq env t1  in
                        match uu____18372 with
                        | (t',aq) ->
                            let uu____18395 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____18395, aq)))
                 in
              FStar_All.pipe_right uu____18280 FStar_List.unzip  in
            (match uu____18242 with
             | (targs,aqs) ->
                 let tup =
                   let uu____18582 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____18582
                    in
                 let uu____18607 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____18607, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____18674 =
              let uu____18696 =
                let uu____18710 =
                  let uu____18724 =
                    FStar_All.pipe_left
                      (fun _18758  -> FStar_Util.Inl _18758)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____18724]  in
                FStar_List.append binders uu____18710  in
              FStar_List.fold_left
                (fun uu____18836  ->
                   fun b  ->
                     match uu____18836 with
                     | (env1,tparams,typs) ->
                         let uu____18924 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____18972 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____18972)
                            in
                         (match uu____18924 with
                          | (xopt,t1) ->
                              let uu____19030 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____19051 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____19051)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____19030 with
                               | (env2,x) ->
                                   let uu____19105 =
                                     let uu____19108 =
                                       let uu____19111 =
                                         let uu____19112 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____19112
                                          in
                                       [uu____19111]  in
                                     FStar_List.append typs uu____19108  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1557_19170 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1557_19170.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1557_19170.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____19105)))) (env, [], [])
                uu____18696
               in
            (match uu____18674 with
             | (env1,uu____19227,targs) ->
                 let tup =
                   let uu____19268 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____19268
                    in
                 let uu____19281 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____19281, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____19338 = uncurry binders t  in
            (match uu____19338 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_19420 =
                   match uu___10_19420 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____19462 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____19462
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____19525 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____19525 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____19582 = aux env [] bs  in (uu____19582, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____19622 = desugar_binder env b  in
            (match uu____19622 with
             | (FStar_Pervasives_Native.None ,uu____19643) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____19680 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____19680 with
                  | ((x,uu____19705),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____19741 =
                        let uu____19750 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____19750  in
                      (uu____19741, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____19899 = FStar_Util.set_is_empty i  in
                    if uu____19899
                    then
                      let uu____19908 = FStar_Util.set_union acc set1  in
                      aux uu____19908 sets2
                    else
                      (let uu____19917 =
                         let uu____19922 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____19922  in
                       FStar_Pervasives_Native.Some uu____19917)
                 in
              let uu____19933 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____19933 sets  in
            ((let uu____19939 = check_disjoint bvss  in
              match uu____19939 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____19951 =
                    let uu____19957 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____19957)
                     in
                  let uu____19961 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____19951 uu____19961);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____19979 =
                FStar_List.fold_left
                  (fun uu____20005  ->
                     fun pat  ->
                       match uu____20005 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____20043,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____20075 =
                                  let uu____20080 = free_type_vars env1 t  in
                                  FStar_List.append uu____20080 ftvs  in
                                (env1, uu____20075)
                            | FStar_Parser_AST.PatAscribed
                                (uu____20091,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____20127 =
                                  let uu____20132 = free_type_vars env1 t  in
                                  let uu____20137 =
                                    let uu____20142 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____20142 ftvs  in
                                  FStar_List.append uu____20132 uu____20137
                                   in
                                (env1, uu____20127)
                            | uu____20155 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____19979 with
              | (uu____20174,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____20194 =
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
                    FStar_List.append uu____20194 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___11_20285 =
                    match uu___11_20285 with
                    | [] ->
                        let uu____20329 = desugar_term_aq env1 body  in
                        (match uu____20329 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____20423 =
                                       let uu____20424 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____20424
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____20423
                                       body1
                                      in
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (sc,
                                          [(pat,
                                             FStar_Pervasives_Native.None,
                                             body2)]))
                                     FStar_Pervasives_Native.None
                                     body2.FStar_Syntax_Syntax.pos
                               | FStar_Pervasives_Native.None  -> body1  in
                             let uu____20567 =
                               let uu____20578 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____20578  in
                             (uu____20567, aq))
                    | p::rest ->
                        let uu____20616 = desugar_binding_pat env1 p  in
                        (match uu____20616 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____20663)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____20699 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____20711 =
                               match b with
                               | LetBinder uu____20776 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____20903) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____21000 =
                                           let uu____21016 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____21016, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____21000
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____21144,uu____21145) ->
                                              let tup2 =
                                                let uu____21158 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____21158
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____21179 =
                                                  let uu____21186 =
                                                    let uu____21187 =
                                                      let uu____21212 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____21223 =
                                                        let uu____21238 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____21251 =
                                                          let uu____21266 =
                                                            let uu____21279 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____21279
                                                             in
                                                          [uu____21266]  in
                                                        uu____21238 ::
                                                          uu____21251
                                                         in
                                                      (uu____21212,
                                                        uu____21223)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____21187
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____21186
                                                   in
                                                uu____21179
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____21366 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____21366
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____21452,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____21454,pats)) ->
                                              let tupn =
                                                let uu____21533 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____21533
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____21566 =
                                                  let uu____21567 =
                                                    let uu____21592 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____21603 =
                                                      let uu____21618 =
                                                        let uu____21633 =
                                                          let uu____21646 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____21646
                                                           in
                                                        [uu____21633]  in
                                                      FStar_List.append args
                                                        uu____21618
                                                       in
                                                    (uu____21592,
                                                      uu____21603)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____21567
                                                   in
                                                mk1 uu____21566  in
                                              let p2 =
                                                let uu____21733 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____21733
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____21812 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____20711 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____21975,uu____21976,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____22020 =
                let uu____22021 = unparen e  in
                uu____22021.FStar_Parser_AST.tm  in
              match uu____22020 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____22053 ->
                  let uu____22054 = desugar_term_aq env e  in
                  (match uu____22054 with
                   | (head1,aq) ->
                       let uu____22083 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____22083, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____22106 ->
            let rec aux args aqs e =
              let uu____22234 =
                let uu____22235 = unparen e  in
                uu____22235.FStar_Parser_AST.tm  in
              match uu____22234 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____22284 = desugar_term_aq env t  in
                  (match uu____22284 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____22378 ->
                  let uu____22379 = desugar_term_aq env e  in
                  (match uu____22379 with
                   | (head1,aq) ->
                       let uu____22425 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____22425, (join_aqs (aq :: aqs))))
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
            let uu____22590 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____22590
        | FStar_Parser_AST.Seq (t1,t2) ->
            let t =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (FStar_Parser_AST.NoLetQualifier,
                     [(FStar_Pervasives_Native.None,
                        ((FStar_Parser_AST.mk_pattern
                            (FStar_Parser_AST.PatWild
                               FStar_Pervasives_Native.None)
                            t1.FStar_Parser_AST.range), t1))], t2))
                top.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let uu____22718 = desugar_term_aq env t  in
            (match uu____22718 with
             | (tm,s) ->
                 let uu____22745 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____22745, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____22781 =
              let uu____22801 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____22801 then desugar_typ_aq else desugar_term_aq  in
            uu____22781 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____22893 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____23120  ->
                        match uu____23120 with
                        | (attr_opt,(p,def)) ->
                            let uu____23227 = is_app_pattern p  in
                            if uu____23227
                            then
                              let uu____23280 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____23280, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____23432 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____23432, def1)
                               | uu____23511 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____23574);
                                           FStar_Parser_AST.prange =
                                             uu____23575;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____23662 =
                                            let uu____23697 =
                                              let uu____23708 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____23708  in
                                            (uu____23697, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____23662, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____23904) ->
                                        if top_level
                                        then
                                          let uu____23964 =
                                            let uu____23999 =
                                              let uu____24010 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____24010  in
                                            (uu____23999, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____23964, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____24205 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____24258 =
                FStar_List.fold_left
                  (fun uu____24369  ->
                     fun uu____24370  ->
                       match (uu____24369, uu____24370) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____24545,uu____24546),uu____24547))
                           ->
                           let uu____24765 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____24817 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____24817 with
                                  | (env2,xx) ->
                                      let uu____24860 =
                                        let uu____24863 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____24863 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____24860))
                             | FStar_Util.Inr l ->
                                 let uu____24899 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____24899, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____24765 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____24258 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____25204 =
                    match uu____25204 with
                    | (attrs_opt,(uu____25276,args,result_t),def) ->
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
                                let uu____25467 = is_comp_type env1 t  in
                                if uu____25467
                                then
                                  ((let uu____25474 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____25494 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____25494))
                                       in
                                    match uu____25474 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____25507 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____25510 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____25510))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____25507
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
                          | uu____25554 ->
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
                              let uu____25630 =
                                let uu____25637 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____25637
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____25630
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
                  let uu____25829 = desugar_term_aq env' body  in
                  (match uu____25829 with
                   | (body1,aq) ->
                       let uu____25858 =
                         let uu____25869 =
                           let uu____25870 =
                             let uu____25895 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____25895)  in
                           FStar_Syntax_Syntax.Tm_let uu____25870  in
                         FStar_All.pipe_left mk1 uu____25869  in
                       (uu____25858, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____26066 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____26066 with
              | (env1,binder,pat1) ->
                  let uu____26092 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____26158 = desugar_term_aq env1 t2  in
                        (match uu____26158 with
                         | (body1,aq) ->
                             let fv =
                               let uu____26194 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____26194
                                 FStar_Pervasives_Native.None
                                in
                             let uu____26195 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____26195, aq))
                    | LocalBinder (x,uu____26304) ->
                        let uu____26315 = desugar_term_aq env1 t2  in
                        (match uu____26315 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____26357;
                                    FStar_Syntax_Syntax.p = uu____26358;_},uu____26359)::[]
                                   -> body1
                               | uu____26395 ->
                                   let uu____26398 =
                                     let uu____26405 =
                                       let uu____26406 =
                                         let uu____26444 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____26455 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____26444, uu____26455)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____26406
                                        in
                                     FStar_Syntax_Syntax.mk uu____26405  in
                                   uu____26398 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____26522 =
                               let uu____26533 =
                                 let uu____26534 =
                                   let uu____26559 =
                                     let uu____26570 =
                                       let uu____26571 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____26571]  in
                                     FStar_Syntax_Subst.close uu____26570
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____26559)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____26534  in
                               FStar_All.pipe_left mk1 uu____26533  in
                             (uu____26522, aq))
                     in
                  (match uu____26092 with | (tm,aq) -> (tm, aq))
               in
            let uu____26732 = FStar_List.hd lbs  in
            (match uu____26732 with
             | (attrs,(head_pat,defn)) ->
                 let uu____26817 = is_rec || (is_app_pattern head_pat)  in
                 if uu____26817
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____26873 =
                let uu____26874 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____26874  in
              mk1 uu____26873  in
            let uu____26881 = desugar_term_aq env t1  in
            (match uu____26881 with
             | (t1',aq1) ->
                 let uu____26908 = desugar_term_aq env t2  in
                 (match uu____26908 with
                  | (t2',aq2) ->
                      let uu____26935 = desugar_term_aq env t3  in
                      (match uu____26935 with
                       | (t3',aq3) ->
                           let uu____26962 =
                             let uu____26971 =
                               let uu____26972 =
                                 let uu____27010 =
                                   let uu____27038 =
                                     let uu____27064 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____27064,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____27096 =
                                     let uu____27124 =
                                       let uu____27150 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____27150,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____27124]  in
                                   uu____27038 :: uu____27096  in
                                 (t1', uu____27010)  in
                               FStar_Syntax_Syntax.Tm_match uu____26972  in
                             mk1 uu____26971  in
                           (uu____26962, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let try_with_lid1 = FStar_Ident.lid_of_path ["try_with"] r  in
            let try_with1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var try_with_lid1) r
                FStar_Parser_AST.Expr
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (try_with1, body, FStar_Parser_AST.Nothing)) r
                top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____27581 =
              match uu____27581 with
              | (pat,wopt,b) ->
                  let uu____27627 = desugar_match_pat env pat  in
                  (match uu____27627 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____27679 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____27679
                          in
                       let uu____27696 = desugar_term_aq env1 b  in
                       (match uu____27696 with
                        | (b1,aq) ->
                            let uu____27721 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____27721, aq)))
               in
            let uu____27726 = desugar_term_aq env e  in
            (match uu____27726 with
             | (e1,aq) ->
                 let uu____27753 =
                   let uu____27804 =
                     let uu____27857 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____27857 FStar_List.unzip  in
                   FStar_All.pipe_right uu____27804
                     (fun uu____28223  ->
                        match uu____28223 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____27753 with
                  | (brs,aqs) ->
                      let uu____28594 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____28594, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____28686 =
              let uu____28724 = is_comp_type env t  in
              if uu____28724
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____28838 = desugar_term_aq env t  in
                 match uu____28838 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____28686 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____29033 = desugar_term_aq env e  in
                 (match uu____29033 with
                  | (e1,aq) ->
                      let uu____29060 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____29060, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____29160,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____29272 = FStar_List.hd fields  in
              match uu____29272 with | (f,uu____29300) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____29405  ->
                        match uu____29405 with
                        | (g,uu____29419) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____29461,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____29520 =
                         let uu____29526 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____29526)
                          in
                       FStar_Errors.raise_error uu____29520
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
                  let uu____29581 =
                    let uu____29599 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____29651  ->
                              match uu____29651 with
                              | (f,uu____29670) ->
                                  let uu____29683 =
                                    let uu____29690 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____29690
                                     in
                                  (uu____29683, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____29599)  in
                  FStar_Parser_AST.Construct uu____29581
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____29761 =
                      let uu____29762 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____29762  in
                    FStar_Parser_AST.mk_term uu____29761
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____29776 =
                      let uu____29799 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____29862  ->
                                match uu____29862 with
                                | (f,uu____29885) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____29799)  in
                    FStar_Parser_AST.Record uu____29776  in
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
            let uu____30024 = desugar_term_aq env recterm1  in
            (match uu____30024 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____30060;
                         FStar_Syntax_Syntax.vars = uu____30061;_},args)
                      ->
                      let uu____30106 =
                        let uu____30115 =
                          let uu____30116 =
                            let uu____30141 =
                              let uu____30152 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____30165 =
                                let uu____30168 =
                                  let uu____30169 =
                                    let uu____30182 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____30182)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____30169
                                   in
                                FStar_Pervasives_Native.Some uu____30168  in
                              FStar_Syntax_Syntax.fvar uu____30152
                                FStar_Syntax_Syntax.delta_constant
                                uu____30165
                               in
                            (uu____30141, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____30116  in
                        FStar_All.pipe_left mk1 uu____30115  in
                      (uu____30106, s)
                  | uu____30257 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____30279 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____30279 with
              | (constrname,is_rec) ->
                  let uu____30318 = desugar_term_aq env e  in
                  (match uu____30318 with
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
                       let uu____30368 =
                         let uu____30377 =
                           let uu____30378 =
                             let uu____30403 =
                               let uu____30414 =
                                 let uu____30423 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____30423
                                  in
                               FStar_Syntax_Syntax.fvar uu____30414
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____30425 =
                               let uu____30440 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____30440]  in
                             (uu____30403, uu____30425)  in
                           FStar_Syntax_Syntax.Tm_app uu____30378  in
                         FStar_All.pipe_left mk1 uu____30377  in
                       (uu____30368, s))))
        | FStar_Parser_AST.NamedTyp (uu____30505,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____30543 =
              let uu____30544 = FStar_Syntax_Subst.compress tm  in
              uu____30544.FStar_Syntax_Syntax.n  in
            (match uu____30543 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____30567 =
                   let uu___2091_30576 =
                     let uu____30585 =
                       let uu____30587 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____30587  in
                     FStar_Syntax_Util.exp_string uu____30585  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2091_30576.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2091_30576.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____30567, noaqs)
             | uu____30600 ->
                 let uu____30601 =
                   let uu____30607 =
                     let uu____30609 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____30609
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____30607)  in
                 FStar_Errors.raise_error uu____30601
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____30628 = desugar_term_aq env e  in
            (match uu____30628 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____30660 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____30660, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____30700 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____30709 =
              let uu____30710 =
                let uu____30726 = desugar_term env e  in (bv, uu____30726)
                 in
              [uu____30710]  in
            (uu____30700, uu____30709)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____30809 =
              let uu____30818 =
                let uu____30819 =
                  let uu____30832 = desugar_term env e  in (uu____30832, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____30819  in
              FStar_All.pipe_left mk1 uu____30818  in
            (uu____30809, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let eta_and_annot rel1 =
              let x = FStar_Ident.gen rel1.FStar_Parser_AST.range  in
              let y = FStar_Ident.gen rel1.FStar_Parser_AST.range  in
              let xt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar x)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let yt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar y)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let pats =
                [FStar_Parser_AST.mk_pattern
                   (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                   rel1.FStar_Parser_AST.range;
                FStar_Parser_AST.mk_pattern
                  (FStar_Parser_AST.PatVar (y, FStar_Pervasives_Native.None))
                  rel1.FStar_Parser_AST.range]
                 in
              let uu____30938 =
                let uu____30939 =
                  let uu____30951 =
                    let uu____30958 =
                      let uu____30959 =
                        let uu____30977 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____31011 =
                          let uu____31018 =
                            let uu____31019 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____31019  in
                          FStar_Parser_AST.mk_term uu____31018
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____30977, uu____31011,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____30959  in
                    FStar_Parser_AST.mk_term uu____30958
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____30951)  in
                FStar_Parser_AST.Abs uu____30939  in
              FStar_Parser_AST.mk_term uu____30938
                rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let rel1 = eta_and_annot rel  in
            let wild r =
              FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r
                FStar_Parser_AST.Expr
               in
            let init1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_init_lid)
                init_expr.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let last_expr =
              let uu____31086 = FStar_List.last steps  in
              match uu____31086 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____31094,uu____31095,last_expr)) -> last_expr
              | uu____31116 -> failwith "impossible: no last_expr on calc"
               in
            let step r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_step_lid) r
                FStar_Parser_AST.Expr
               in
            let finish1 =
              FStar_Parser_AST.mkApp
                (FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Var FStar_Parser_Const.calc_finish_lid)
                   top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                [(rel1, FStar_Parser_AST.Nothing)] top.FStar_Parser_AST.range
               in
            let e =
              FStar_Parser_AST.mkApp init1
                [(init_expr, FStar_Parser_AST.Nothing)]
                init_expr.FStar_Parser_AST.range
               in
            let uu____31187 =
              FStar_List.fold_left
                (fun uu____31217  ->
                   fun uu____31218  ->
                     match (uu____31217, uu____31218) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let pf =
                           let uu____31304 =
                             let uu____31314 =
                               let uu____31324 =
                                 let uu____31334 =
                                   let uu____31344 =
                                     let uu____31352 = eta_and_annot rel2  in
                                     (uu____31352, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____31362 =
                                     let uu____31372 =
                                       let uu____31382 =
                                         let uu____31390 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____31390,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____31400 =
                                         let uu____31410 =
                                           let uu____31418 =
                                             FStar_Parser_AST.thunk just  in
                                           (uu____31418,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____31410]  in
                                       uu____31382 :: uu____31400  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____31372
                                      in
                                   uu____31344 :: uu____31362  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____31334
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____31324
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____31314
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____31304
                             just.FStar_Parser_AST.range
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____31187 with
             | (e1,uu____31517) ->
                 let e2 =
                   let uu____31537 =
                     let uu____31547 =
                       let uu____31557 =
                         let uu____31567 =
                           let uu____31575 = FStar_Parser_AST.thunk e1  in
                           (uu____31575, FStar_Parser_AST.Nothing)  in
                         [uu____31567]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____31557  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____31547  in
                   FStar_Parser_AST.mkApp finish1 uu____31537
                     init_expr.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____31619 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____31620 = desugar_formula env top  in
            (uu____31620, noaqs)
        | uu____31633 ->
            let uu____31634 =
              let uu____31640 =
                let uu____31642 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____31642  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____31640)  in
            FStar_Errors.raise_error uu____31634 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____31659 -> false
    | uu____31678 -> true

and (desugar_args :
  FStar_Syntax_DsEnv.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____31733  ->
              match uu____31733 with
              | (a,imp) ->
                  let uu____31759 = desugar_term env a  in
                  arg_withimp_e imp uu____31759))

and (desugar_comp :
  FStar_Range.range ->
    Prims.bool ->
      FStar_Syntax_DsEnv.env ->
        FStar_Parser_AST.term ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun allow_type_promotion  ->
      fun env  ->
        fun t  ->
          let fail1 err = FStar_Errors.raise_error err r  in
          let is_requires uu____31814 =
            match uu____31814 with
            | (t1,uu____31824) ->
                let uu____31831 =
                  let uu____31832 = unparen t1  in
                  uu____31832.FStar_Parser_AST.tm  in
                (match uu____31831 with
                 | FStar_Parser_AST.Requires uu____31840 -> true
                 | uu____31852 -> false)
             in
          let is_ensures uu____31867 =
            match uu____31867 with
            | (t1,uu____31877) ->
                let uu____31884 =
                  let uu____31885 = unparen t1  in
                  uu____31885.FStar_Parser_AST.tm  in
                (match uu____31884 with
                 | FStar_Parser_AST.Ensures uu____31893 -> true
                 | uu____31905 -> false)
             in
          let is_app head1 uu____31926 =
            match uu____31926 with
            | (t1,uu____31937) ->
                let uu____31944 =
                  let uu____31945 = unparen t1  in
                  uu____31945.FStar_Parser_AST.tm  in
                (match uu____31944 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____31954;
                        FStar_Parser_AST.level = uu____31955;_},uu____31956,uu____31957)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____31972 -> false)
             in
          let is_smt_pat uu____31987 =
            match uu____31987 with
            | (t1,uu____31997) ->
                let uu____32004 =
                  let uu____32005 = unparen t1  in
                  uu____32005.FStar_Parser_AST.tm  in
                (match uu____32004 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____32015);
                               FStar_Parser_AST.range = uu____32016;
                               FStar_Parser_AST.level = uu____32017;_},uu____32018)::uu____32019::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                 smtpat;
                               FStar_Parser_AST.range = uu____32108;
                               FStar_Parser_AST.level = uu____32109;_},uu____32110)::uu____32111::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____32174 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____32225 = head_and_args t1  in
            match uu____32225 with
            | (head1,args) ->
                (match head1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma"
                     ->
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
                       ((FStar_Parser_AST.mk_term req
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing)
                        in
                     let thunk_ens uu____32381 =
                       match uu____32381 with
                       | (e,i) ->
                           let uu____32404 = FStar_Parser_AST.thunk e  in
                           (uu____32404, i)
                        in
                     let fail_lemma uu____32428 =
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
                       let msg = FStar_String.concat "\n\t" expected_one_of
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_InvalidLemmaArgument,
                           (Prims.op_Hat
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
                           let uu____32582 =
                             let uu____32592 =
                               let uu____32602 = thunk_ens ens  in
                               [uu____32602; nil_pat]  in
                             req_true :: uu____32592  in
                           unit_tm :: uu____32582
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____32682 =
                             let uu____32692 =
                               let uu____32702 = thunk_ens ens  in
                               [uu____32702; nil_pat]  in
                             req :: uu____32692  in
                           unit_tm :: uu____32682
                       | ens::smtpat::[] when
                           (((let uu____32784 = is_requires ens  in
                              Prims.op_Negation uu____32784) &&
                               (let uu____32787 = is_smt_pat ens  in
                                Prims.op_Negation uu____32787))
                              &&
                              (let uu____32790 = is_decreases ens  in
                               Prims.op_Negation uu____32790))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____32792 =
                             let uu____32802 =
                               let uu____32812 = thunk_ens ens  in
                               [uu____32812; smtpat]  in
                             req_true :: uu____32802  in
                           unit_tm :: uu____32792
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____32892 =
                             let uu____32902 =
                               let uu____32912 = thunk_ens ens  in
                               [uu____32912; nil_pat; dec]  in
                             req_true :: uu____32902  in
                           unit_tm :: uu____32892
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____33014 =
                             let uu____33024 =
                               let uu____33034 = thunk_ens ens  in
                               [uu____33034; smtpat; dec]  in
                             req_true :: uu____33024  in
                           unit_tm :: uu____33014
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____33136 =
                             let uu____33146 =
                               let uu____33156 = thunk_ens ens  in
                               [uu____33156; nil_pat; dec]  in
                             req :: uu____33146  in
                           unit_tm :: uu____33136
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____33258 =
                             let uu____33268 =
                               let uu____33278 = thunk_ens ens  in
                               [uu____33278; smtpat]  in
                             req :: uu____33268  in
                           unit_tm :: uu____33258
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____33388 =
                             let uu____33398 =
                               let uu____33408 = thunk_ens ens  in
                               [uu____33408; dec; smtpat]  in
                             req :: uu____33398  in
                           unit_tm :: uu____33388
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____33513 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____33513, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____33560 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____33560
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____33571 =
                       let uu____33582 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____33582, [])  in
                     (uu____33571, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____33623 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____33623
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____33634 =
                       let uu____33645 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____33645, [])  in
                     (uu____33634, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____33690 =
                       let uu____33701 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____33701, [])  in
                     (uu____33690, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____33752 when allow_type_promotion ->
                     let default_effect =
                       let uu____33762 = FStar_Options.ml_ish ()  in
                       if uu____33762
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____33772 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____33772
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____33779 =
                       let uu____33790 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____33790, [])  in
                     (uu____33779, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____33841 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____33867 = pre_process_comp_typ t  in
          match uu____33867 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____33951 =
                    let uu____33957 =
                      let uu____33959 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____33959
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____33957)
                     in
                  fail1 uu____33951)
               else ();
               (let is_universe uu____33978 =
                  match uu____33978 with
                  | (uu____33987,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____33995 = FStar_Util.take is_universe args  in
                match uu____33995 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____34082  ->
                           match uu____34082 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____34098 =
                      let uu____34119 = FStar_List.hd args1  in
                      let uu____34134 = FStar_List.tl args1  in
                      (uu____34119, uu____34134)  in
                    (match uu____34098 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____34232 =
                           let is_decrease uu____34283 =
                             match uu____34283 with
                             | (t1,uu____34298) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____34317;
                                         FStar_Syntax_Syntax.vars =
                                           uu____34318;_},uu____34319::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____34385 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____34232 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____34546  ->
                                        match uu____34546 with
                                        | (t1,uu____34560) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____34577,(arg,uu____34579)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____34646 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____34667 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____34683 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____34683
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____34694 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____34694
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____34708 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____34708
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____34715 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____34715
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____34722 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____34722
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____34729 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____34729
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____34754 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____34754
                                      then
                                        match rest2 with
                                        | req::ens::(pat,aq)::[] ->
                                            let pat1 =
                                              match pat.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv when
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
                                                    let uu____34916 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____34916
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
                                              | uu____34957 -> pat  in
                                            let uu____34958 =
                                              let uu____34973 =
                                                let uu____34988 =
                                                  let uu____35001 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____35001, aq)  in
                                                [uu____34988]  in
                                              ens :: uu____34973  in
                                            req :: uu____34958
                                        | uu____35074 -> rest2
                                      else rest2  in
                                    FStar_Syntax_Syntax.mk_Comp
                                      {
                                        FStar_Syntax_Syntax.comp_univs =
                                          universes1;
                                        FStar_Syntax_Syntax.effect_name = eff;
                                        FStar_Syntax_Syntax.result_typ =
                                          result_typ;
                                        FStar_Syntax_Syntax.effect_args =
                                          rest3;
                                        FStar_Syntax_Syntax.flags =
                                          (FStar_List.append flags1
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
        | uu____35145 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2398_35195 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2398_35195.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2398_35195.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2405_35299 = b  in
             {
               FStar_Parser_AST.b = (uu___2405_35299.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2405_35299.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2405_35299.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____35349 body1 =
          match uu____35349 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____35437::uu____35438) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____35476 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2424_35526 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2424_35526.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2424_35526.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____35639 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____35639))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____35720 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____35720 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2437_35759 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2437_35759.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2437_35759.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____35799 =
                     let uu____35810 =
                       let uu____35811 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____35811]  in
                     no_annot_abs uu____35810 body2  in
                   FStar_All.pipe_left setpos uu____35799  in
                 let uu____35855 =
                   let uu____35856 =
                     let uu____35881 =
                       let uu____35892 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____35892
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____35902 =
                       let uu____35917 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____35917]  in
                     (uu____35881, uu____35902)  in
                   FStar_Syntax_Syntax.Tm_app uu____35856  in
                 FStar_All.pipe_left mk1 uu____35855)
        | uu____35980 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____36123 = q (rest, pats, body)  in
              let uu____36133 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____36123 uu____36133
                FStar_Parser_AST.Formula
               in
            let uu____36134 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____36134 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____36170 -> failwith "impossible"  in
      let uu____36181 =
        let uu____36182 = unparen f  in uu____36182.FStar_Parser_AST.tm  in
      match uu____36181 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____36227,uu____36228) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____36280,uu____36281) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____36417 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____36417
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____36526 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____36526
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____36674 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____36683 =
        FStar_List.fold_left
          (fun uu____36730  ->
             fun b  ->
               match uu____36730 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2516_36804 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2516_36804.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2516_36804.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2516_36804.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____36846 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____36846 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2526_36894 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2526_36894.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2526_36894.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____36905 =
                               let uu____36917 =
                                 let uu____36927 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____36927)  in
                               uu____36917 :: out  in
                             (env2, uu____36905))
                    | uu____36953 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____36683 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____37092 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____37092)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____37123 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____37123)
      | FStar_Parser_AST.TVariable x ->
          let uu____37145 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____37145)
      | FStar_Parser_AST.NoName t ->
          let uu____37168 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____37168)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

and (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term) ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) * FStar_Syntax_DsEnv.env))
  =
  fun env  ->
    fun imp  ->
      fun uu___12_37202  ->
        match uu___12_37202 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____37247 = FStar_Syntax_Syntax.null_binder k  in
            (uu____37247, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____37288 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____37288 with
             | (env1,a1) ->
                 let uu____37325 =
                   let uu____37337 = trans_aqual env1 imp  in
                   ((let uu___2560_37348 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2560_37348.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2560_37348.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____37337)
                    in
                 (uu____37325, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___13_37371  ->
      match uu___13_37371 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____37378 =
            let uu____37379 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____37379  in
          FStar_Pervasives_Native.Some uu____37378
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____37417) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____37431) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____37454 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____37499 = binder_ident b  in
         FStar_Common.list_of_option uu____37499) bs
  
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
               (fun uu___14_37553  ->
                  match uu___14_37553 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____37558 -> false))
           in
        let quals2 q =
          let uu____37572 =
            (let uu____37576 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____37576) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____37572
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____37623 = FStar_Ident.range_of_lid disc_name  in
                let uu____37624 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____37623;
                  FStar_Syntax_Syntax.sigquals = uu____37624;
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
            let uu____37691 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____37754  ->
                        match uu____37754 with
                        | (x,uu____37775) ->
                            let uu____37790 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____37790 with
                             | (field_name,uu____37812) ->
                                 let only_decl =
                                   ((let uu____37835 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____37835)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____37845 =
                                        let uu____37847 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____37847.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____37845)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____37873 =
                                       FStar_List.filter
                                         (fun uu___15_37877  ->
                                            match uu___15_37877 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____37880 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____37873
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___16_37895  ->
                                             match uu___16_37895 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____37900 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____37919 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____37919;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____37955 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____37955
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____37980 =
                                        let uu____37993 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____37993  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____37980;
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
                                      let uu____38027 =
                                        let uu____38028 =
                                          let uu____38039 =
                                            let uu____38046 =
                                              let uu____38055 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____38055
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____38046]  in
                                          ((false, [lb]), uu____38039)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____38028
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____38027;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____37691 FStar_List.flatten
  
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
            (lid,uu____38245,t,uu____38247,n1,uu____38249) when
            let uu____38288 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____38288 ->
            let uu____38290 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____38290 with
             | (formals,uu____38322) ->
                 (match formals with
                  | [] -> []
                  | uu____38384 ->
                      let filter_records uu___17_38405 =
                        match uu___17_38405 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____38408,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____38434 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____38436 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____38436 with
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
                      let uu____38448 = FStar_Util.first_N n1 formals  in
                      (match uu____38448 with
                       | (uu____38497,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____38551 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
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
                    let uu____38686 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____38686
                    then
                      let uu____38692 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____38692
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____38710 =
                      let uu____38723 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____38723  in
                    let uu____38738 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____38760 =
                          let uu____38771 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____38771  in
                        FStar_Syntax_Util.arrow typars uu____38760
                      else FStar_Syntax_Syntax.tun  in
                    let uu____38796 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____38710;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____38738;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____38796;
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
          (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___18_38907 =
            match uu___18_38907 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____38911,uu____38912) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____38940,uu____38941,uu____38942) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____38976,uu____38977,uu____38978) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____39036,uu____39037,uu____39038) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____39126) ->
                let uu____39137 =
                  let uu____39138 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____39138  in
                FStar_Parser_AST.mk_term uu____39137 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____39154 =
                  let uu____39155 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____39155  in
                FStar_Parser_AST.mk_term uu____39154 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____39169) ->
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
              | uu____39267 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____39289 =
                     let uu____39290 =
                       let uu____39303 = binder_to_term b  in
                       (out, uu____39303, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____39290  in
                   FStar_Parser_AST.mk_term uu____39289
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___19_39329 =
            match uu___19_39329 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____39433  ->
                       match uu____39433 with
                       | (x,t,uu____39453) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____39480 =
                    let uu____39487 =
                      let uu____39488 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____39488  in
                    FStar_Parser_AST.mk_term uu____39487
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____39480 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____39522 = binder_idents parms  in id1 ::
                    uu____39522
                   in
                (FStar_List.iter
                   (fun uu____39549  ->
                      match uu____39549 with
                      | (f,uu____39564,uu____39565) ->
                          let uu____39580 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____39580
                          then
                            let uu____39589 =
                              let uu____39595 =
                                let uu____39597 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____39597
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____39595)
                               in
                            FStar_Errors.raise_error uu____39589
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____39603 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____39646  ->
                            match uu____39646 with
                            | (x,uu____39663,uu____39664) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____39603)))
            | uu____39766 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___20_39820 =
            match uu___20_39820 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____39874 = typars_of_binders _env binders  in
                (match uu____39874 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____39960 =
                         let uu____39967 =
                           let uu____39968 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____39968  in
                         FStar_Parser_AST.mk_term uu____39967
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____39960 binders  in
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
            | uu____40051 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____40117 =
              FStar_List.fold_left
                (fun uu____40166  ->
                   fun uu____40167  ->
                     match (uu____40166, uu____40167) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____40291 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____40291 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____40117 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____40479 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____40479
                | uu____40489 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____40509 = desugar_abstract_tc quals env [] tc  in
              (match uu____40509 with
               | (uu____40534,uu____40535,se,uu____40537) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____40571,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____40622 =
                                 let uu____40624 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____40624  in
                               if uu____40622
                               then
                                 let uu____40627 =
                                   let uu____40633 =
                                     let uu____40635 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____40635
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____40633)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____40627
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
                           | uu____40665 ->
                               let uu____40666 =
                                 let uu____40673 =
                                   let uu____40674 =
                                     let uu____40698 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____40698)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____40674
                                    in
                                 FStar_Syntax_Syntax.mk uu____40673  in
                               uu____40666 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2835_40728 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2835_40728.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2835_40728.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2835_40728.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____40749 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____40758 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____40758
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____40813 = typars_of_binders env binders  in
              (match uu____40813 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____40873 =
                           FStar_Util.for_some
                             (fun uu___21_40876  ->
                                match uu___21_40876 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____40879 -> false) quals
                            in
                         if uu____40873
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____40905 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____40905
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____40928 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___22_40934  ->
                               match uu___22_40934 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____40937 -> false))
                        in
                     if uu____40928
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____40969 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____40969
                     then
                       let uu____40980 =
                         let uu____40990 =
                           let uu____40991 = unparen t  in
                           uu____40991.FStar_Parser_AST.tm  in
                         match uu____40990 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____41035 =
                               match FStar_List.rev args with
                               | (last_arg,uu____41080)::args_rev ->
                                   let uu____41104 =
                                     let uu____41105 = unparen last_arg  in
                                     uu____41105.FStar_Parser_AST.tm  in
                                   (match uu____41104 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____41157 -> ([], args))
                               | uu____41175 -> ([], args)  in
                             (match uu____41035 with
                              | (cattributes,args1) ->
                                  let uu____41241 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____41241))
                         | uu____41262 -> (t, [])  in
                       match uu____40980 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range false
                               env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___23_41315  ->
                                     match uu___23_41315 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____41318 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____41369)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____41407 = tycon_record_as_variant trec  in
              (match uu____41407 with
               | (t,fs) ->
                   let uu____41430 =
                     let uu____41433 =
                       let uu____41434 =
                         let uu____41447 =
                           let uu____41452 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____41452  in
                         (uu____41447, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____41434  in
                     uu____41433 :: quals  in
                   desugar_tycon env d uu____41430 [t])
          | uu____41469::uu____41470 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____41729 = et  in
                match uu____41729 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____42084 ->
                         let trec = tc  in
                         let uu____42122 = tycon_record_as_variant trec  in
                         (match uu____42122 with
                          | (t,fs) ->
                              let uu____42213 =
                                let uu____42216 =
                                  let uu____42217 =
                                    let uu____42230 =
                                      let uu____42235 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____42235  in
                                    (uu____42230, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____42217
                                   in
                                uu____42216 :: quals1  in
                              collect_tcs uu____42213 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____42390 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____42390 with
                          | (env2,uu____42493,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____42774 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____42774 with
                          | (env2,uu____42877,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____43108 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____43183 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____43183 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___25_43990  ->
                             match uu___25_43990 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____44095,uu____44096);
                                    FStar_Syntax_Syntax.sigrng = uu____44097;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____44098;
                                    FStar_Syntax_Syntax.sigmeta = uu____44099;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____44100;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____44254 =
                                     typars_of_binders env1 binders  in
                                   match uu____44254 with
                                   | (env2,tpars1) ->
                                       let uu____44300 =
                                         push_tparams env2 tpars1  in
                                       (match uu____44300 with
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
                                 let uu____44356 =
                                   let uu____44389 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____44389)
                                    in
                                 [uu____44356]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____44522);
                                    FStar_Syntax_Syntax.sigrng = uu____44523;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____44525;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____44526;_},constrs,tconstr,quals1)
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
                                 let uu____44754 = push_tparams env1 tpars
                                    in
                                 (match uu____44754 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____44865  ->
                                             match uu____44865 with
                                             | (x,uu____44887) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____44913 =
                                        let uu____44958 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____45132  ->
                                                  match uu____45132 with
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
                                                        let uu____45284 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____45284
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
                                                                uu___24_45309
                                                                 ->
                                                                match uu___24_45309
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____45325
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____45338 =
                                                        let uu____45371 =
                                                          let uu____45382 =
                                                            let uu____45383 =
                                                              let uu____45415
                                                                =
                                                                let uu____45424
                                                                  =
                                                                  let uu____45435
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____45435
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____45424
                                                                 in
                                                              (name, univs1,
                                                                uu____45415,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____45383
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____45382;
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
                                                          uu____45371)
                                                         in
                                                      (name, uu____45338)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____44958
                                         in
                                      (match uu____44913 with
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
                             | uu____45880 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____46087  ->
                             match uu____46087 with
                             | (name_doc,uu____46131,uu____46132) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____46275  ->
                             match uu____46275 with
                             | (uu____46313,uu____46314,se) -> se))
                      in
                   let uu____46368 =
                     let uu____46385 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____46385 rng
                      in
                   (match uu____46368 with
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
                               (fun uu____46528  ->
                                  match uu____46528 with
                                  | (uu____46568,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____46679,tps,k,uu____46682,constrs)
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
                                      let uu____46735 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____46780 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____46822,uu____46823,uu____46824,uu____46825,uu____46826)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____46865
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____46780
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____46884 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___26_46891  ->
                                                          match uu___26_46891
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____46893 ->
                                                              true
                                                          | uu____46907 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____46884))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____46735
                                  | uu____46909 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____46950  ->
                                 match uu____46950 with
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
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list))
  =
  fun env  ->
    fun binders  ->
      let uu____47040 =
        FStar_List.fold_left
          (fun uu____47089  ->
             fun b  ->
               match uu____47089 with
               | (env1,binders1) ->
                   let uu____47157 = desugar_binder env1 b  in
                   (match uu____47157 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____47205 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____47205 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____47296 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____47040 with
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
          let uu____47454 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___27_47461  ->
                    match uu___27_47461 with
                    | FStar_Syntax_Syntax.Reflectable uu____47463 -> true
                    | uu____47469 -> false))
             in
          if uu____47454
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____47482 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____47482
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
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun at1  ->
      let uu____47565 = FStar_Syntax_Util.head_and_args at1  in
      match uu____47565 with
      | (hd1,args) ->
          let uu____47642 =
            let uu____47661 =
              let uu____47662 = FStar_Syntax_Subst.compress hd1  in
              uu____47662.FStar_Syntax_Syntax.n  in
            (uu____47661, args)  in
          (match uu____47642 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____47699)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____47757 =
                 let uu____47762 =
                   let uu____47771 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____47771 a1  in
                 uu____47762 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____47757 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____47797 =
                      let uu____47806 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____47806, b)  in
                    FStar_Pervasives_Native.Some uu____47797
                | uu____47823 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____47888) when
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
           | uu____47934 -> FStar_Pervasives_Native.None)
  
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                FStar_Parser_AST.term Prims.list ->
                  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                    Prims.list))
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
                  let uu____48206 = desugar_binders monad_env eff_binders  in
                  match uu____48206 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____48274 =
                          let uu____48276 =
                            let uu____48290 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____48290  in
                          FStar_List.length uu____48276  in
                        uu____48274 = (Prims.parse_int "1")  in
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
                            (uu____48407,uu____48408,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____48410,uu____48411,uu____48412),uu____48413)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____48474 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____48477 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____48509 = name_of_eff_decl decl  in
                             FStar_List.mem uu____48509 mandatory_members)
                          eff_decls
                         in
                      (match uu____48477 with
                       | (mandatory_members_decls,actions) ->
                           let uu____48553 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____48607  ->
                                     fun decl  ->
                                       match uu____48607 with
                                       | (env2,out) ->
                                           let uu____48652 =
                                             desugar_decl env2 decl  in
                                           (match uu____48652 with
                                            | (env3,ses) ->
                                                let uu____48670 =
                                                  let uu____48678 =
                                                    FStar_List.hd ses  in
                                                  uu____48678 :: out  in
                                                (env3, uu____48670)))
                                  (env1, []))
                              in
                           (match uu____48553 with
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
                                              (uu____48852,uu____48853,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____48856,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____48857,(def,uu____48859)::
                                                      (cps_type,uu____48861)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____48862;
                                                   FStar_Parser_AST.level =
                                                     uu____48863;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____48972 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____48972 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____49035 =
                                                     let uu____49056 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____49065 =
                                                       let uu____49074 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____49074
                                                        in
                                                     let uu____49094 =
                                                       let uu____49103 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____49103
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____49056;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____49065;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____49094
                                                     }  in
                                                   (uu____49035, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____49137,uu____49138,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____49141,defn),doc1)::[])
                                              when for_free ->
                                              let uu____49204 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____49204 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____49267 =
                                                     let uu____49288 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____49297 =
                                                       let uu____49306 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____49306
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____49288;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____49297;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____49267, doc1))
                                          | uu____49340 ->
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
                                    let uu____49448 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____49448
                                     in
                                  let uu____49454 =
                                    let uu____49463 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____49463
                                     in
                                  ([], uu____49454)  in
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
                                      let uu____49542 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____49542)  in
                                    let uu____49565 =
                                      let uu____49566 =
                                        let uu____49607 =
                                          let uu____49616 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____49616
                                           in
                                        let uu____49638 = lookup1 "return"
                                           in
                                        let uu____49640 = lookup1 "bind"  in
                                        let uu____49642 =
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
                                            uu____49607;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____49638;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____49640;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____49642
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____49566
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____49565;
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
                                         (fun uu___28_49667  ->
                                            match uu___28_49667 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____49670 -> true
                                            | uu____49676 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____49705 =
                                       let uu____49706 =
                                         let uu____49747 =
                                           lookup1 "return_wp"  in
                                         let uu____49749 = lookup1 "bind_wp"
                                            in
                                         let uu____49751 =
                                           lookup1 "if_then_else"  in
                                         let uu____49753 = lookup1 "ite_wp"
                                            in
                                         let uu____49755 = lookup1 "stronger"
                                            in
                                         let uu____49757 = lookup1 "close_wp"
                                            in
                                         let uu____49759 = lookup1 "assert_p"
                                            in
                                         let uu____49761 = lookup1 "assume_p"
                                            in
                                         let uu____49763 = lookup1 "null_wp"
                                            in
                                         let uu____49765 = lookup1 "trivial"
                                            in
                                         let uu____49767 =
                                           if rr
                                           then
                                             let uu____49781 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____49781
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____49821 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____49826 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____49831 =
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
                                             uu____49747;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____49749;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____49751;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____49753;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____49755;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____49757;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____49759;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____49761;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____49763;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____49765;
                                           FStar_Syntax_Syntax.repr =
                                             uu____49767;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____49821;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____49826;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____49831
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____49706
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____49705;
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
                                          fun uu____49894  ->
                                            match uu____49894 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____49938 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____49938
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
                (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                  Prims.list))
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
                let uu____50005 = desugar_binders env1 eff_binders  in
                match uu____50005 with
                | (env2,binders) ->
                    let uu____50062 =
                      let uu____50097 = head_and_args defn  in
                      match uu____50097 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____50192 ->
                                let uu____50193 =
                                  let uu____50199 =
                                    let uu____50201 =
                                      let uu____50203 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____50203 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____50201  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____50199)
                                   in
                                FStar_Errors.raise_error uu____50193
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____50273 =
                            match FStar_List.rev args with
                            | (last_arg,uu____50318)::args_rev ->
                                let uu____50342 =
                                  let uu____50343 = unparen last_arg  in
                                  uu____50343.FStar_Parser_AST.tm  in
                                (match uu____50342 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____50395 -> ([], args))
                            | uu____50413 -> ([], args)  in
                          (match uu____50273 with
                           | (cattributes,args1) ->
                               let uu____50504 = desugar_args env2 args1  in
                               let uu____50505 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____50504, uu____50505))
                       in
                    (match uu____50062 with
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
                          (let uu____50631 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____50631 with
                           | (ed_binders,uu____50654,ed_binders_opening) ->
                               let sub' shift_n uu____50687 =
                                 match uu____50687 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____50728 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____50728 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____50734 =
                                       let uu____50735 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____50735)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____50734
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____50824 =
                                   let uu____50833 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____50833
                                    in
                                 let uu____50868 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____50869 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____50870 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____50871 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____50872 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____50873 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____50874 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____50875 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____50876 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____50877 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____50878 =
                                   let uu____50887 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____50887
                                    in
                                 let uu____50922 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____50923 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____50924 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____50985 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____50994 =
                                          let uu____51003 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____51003
                                           in
                                        let uu____51038 =
                                          let uu____51047 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____51047
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____50985;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____50994;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____51038
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
                                     uu____50824;
                                   FStar_Syntax_Syntax.ret_wp = uu____50868;
                                   FStar_Syntax_Syntax.bind_wp = uu____50869;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____50870;
                                   FStar_Syntax_Syntax.ite_wp = uu____50871;
                                   FStar_Syntax_Syntax.stronger = uu____50872;
                                   FStar_Syntax_Syntax.close_wp = uu____50873;
                                   FStar_Syntax_Syntax.assert_p = uu____50874;
                                   FStar_Syntax_Syntax.assume_p = uu____50875;
                                   FStar_Syntax_Syntax.null_wp = uu____50876;
                                   FStar_Syntax_Syntax.trivial = uu____50877;
                                   FStar_Syntax_Syntax.repr = uu____50878;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____50922;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____50923;
                                   FStar_Syntax_Syntax.actions = uu____50924;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____51095 =
                                     let uu____51097 =
                                       let uu____51111 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____51111
                                        in
                                     FStar_List.length uu____51097  in
                                   uu____51095 = (Prims.parse_int "1")  in
                                 let uu____51167 =
                                   let uu____51170 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____51170 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____51167;
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
                                             let uu____51232 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____51232
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____51244 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____51244
                                 then
                                   let reflect_lid =
                                     let uu____51259 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____51259
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
    let uu____51325 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____51325 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____51414 ->
              let uu____51417 =
                let uu____51419 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____51419
                 in
              Prims.op_Hat "\n  " uu____51417
          | uu____51422 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____51441  ->
               match uu____51441 with
               | (k,v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.op_Hat k (Prims.op_Hat ": " v1))
                   else FStar_Pervasives_Native.None) kv
           in
        let other1 =
          if other <> []
          then Prims.op_Hat (FStar_String.concat "\n" other) "\n"
          else ""  in
        let str =
          Prims.op_Hat summary (Prims.op_Hat pp (Prims.op_Hat other1 text))
           in
        let fv =
          let uu____51494 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____51494
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____51513 =
          let uu____51528 = FStar_Syntax_Syntax.as_arg arg  in [uu____51528]
           in
        FStar_Syntax_Util.mk_app fv uu____51513

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____51576 = desugar_decl_noattrs env d  in
      match uu____51576 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____51609 = mk_comment_attr d  in uu____51609 :: attrs1  in
          let uu____51622 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3392_51652 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3392_51652.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3392_51652.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3392_51652.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3392_51652.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3394_51665 = sigelt  in
                      let uu____51676 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____51694 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____51694) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3394_51665.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3394_51665.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3394_51665.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3394_51665.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____51676
                      })) sigelts
             in
          (env1, uu____51622)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____51725 = desugar_decl_aux env d  in
      match uu____51725 with
      | (env1,ses) ->
          let uu____51736 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____51736)

and (desugar_decl_noattrs :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
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
      | FStar_Parser_AST.Fsdoc uu____51812 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____51844 = FStar_Syntax_DsEnv.iface env  in
          if uu____51844
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____51859 =
               let uu____51861 =
                 let uu____51863 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____51864 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____51863
                   uu____51864
                  in
               Prims.op_Negation uu____51861  in
             if uu____51859
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____51886 =
                  let uu____51888 =
                    let uu____51890 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____51890 lid  in
                  Prims.op_Negation uu____51888  in
                if uu____51886
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____51904 =
                     let uu____51906 =
                       let uu____51908 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____51908
                         lid
                        in
                     Prims.op_Negation uu____51906  in
                   if uu____51904
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____51952 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____51952, [])
      | FStar_Parser_AST.Tycon (is_effect,typeclass,tcs) ->
          let quals = d.FStar_Parser_AST.quals  in
          let quals1 =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: quals
            else quals  in
          let quals2 =
            if typeclass
            then
              match tcs with
              | (FStar_Parser_AST.TyconRecord uu____51998,uu____51999)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____52052 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____52079  ->
                 match uu____52079 with | (x,uu____52087) -> x) tcs
             in
          let uu____52092 =
            let uu____52097 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____52097 tcs1  in
          (match uu____52092 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____52130 =
                   let uu____52131 =
                     let uu____52143 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____52143  in
                   [uu____52131]  in
                 let uu____52176 =
                   let uu____52187 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____52198 =
                     let uu____52213 =
                       let uu____52226 =
                         let uu____52235 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____52235  in
                       FStar_Syntax_Syntax.as_arg uu____52226  in
                     [uu____52213]  in
                   FStar_Syntax_Util.mk_app uu____52187 uu____52198  in
                 FStar_Syntax_Util.abs uu____52130 uu____52176
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____52308,id1))::uu____52310 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____52327::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____52333 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____52333 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____52355 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____52355]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____52420) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____52458,uu____52459,uu____52460,uu____52461,uu____52462)
                     ->
                     let uu____52503 =
                       let uu____52514 =
                         let uu____52515 =
                           let uu____52530 = mkclass lid  in
                           (meths, uu____52530)  in
                         FStar_Syntax_Syntax.Sig_splice uu____52515  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____52514;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____52503]
                 | uu____52563 -> []  in
               let extra =
                 if typeclass
                 then
                   let meths = FStar_List.concatMap get_meths ses  in
                   FStar_List.concatMap (splice_decl meths) ses
                 else []  in
               let env2 =
                 FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
                   extra
                  in
               (env2, (FStar_List.append ses extra)))
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____52660;
                    FStar_Parser_AST.prange = uu____52661;_},uu____52662)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____52692;
                    FStar_Parser_AST.prange = uu____52693;_},uu____52694)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____52730;
                         FStar_Parser_AST.prange = uu____52731;_},uu____52732);
                    FStar_Parser_AST.prange = uu____52733;_},uu____52734)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____52790;
                         FStar_Parser_AST.prange = uu____52791;_},uu____52792);
                    FStar_Parser_AST.prange = uu____52793;_},uu____52794)::[]
                   -> false
               | (p,uu____52857)::[] ->
                   let uu____52886 = is_app_pattern p  in
                   Prims.op_Negation uu____52886
               | uu____52888 -> false)
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
            let uu____53022 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____53022 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____53047 =
                     let uu____53048 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____53048.FStar_Syntax_Syntax.n  in
                   match uu____53047 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____53074) ->
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
                         | uu____53177::uu____53178 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____53185 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___29_53222  ->
                                     match uu___29_53222 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____53232;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____53233;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____53234;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____53235;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____53236;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____53237;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____53238;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____53281;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____53282;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____53283;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____53284;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____53285;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____53286;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____53333 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____53382  ->
                                   match uu____53382 with
                                   | (uu____53404,(uu____53405,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____53333
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____53446 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____53446
                         then
                           let uu____53452 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3589_53530 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3591_53554 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3591_53554.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3591_53554.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3589_53530.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3589_53530.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3589_53530.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3589_53530.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3589_53530.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3589_53530.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____53452)
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
                   | uu____53672 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____53680 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____53734 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____53680 with
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
                       let uu___3617_53823 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3617_53823.FStar_Parser_AST.prange)
                       }
                   | uu____53842 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3621_53849 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3621_53849.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___3621_53849.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3621_53849.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____53927 id1 =
                   match uu____53927 with
                   | (env1,ses) ->
                       let main =
                         let uu____53976 =
                           let uu____53977 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____53977  in
                         FStar_Parser_AST.mk_term uu____53976
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
                       let uu____54137 = desugar_decl env1 id_decl  in
                       (match uu____54137 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____54172 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____54172 FStar_Util.set_elements
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
            let uu____54309 = close_fun env t  in
            desugar_term env uu____54309  in
          let quals1 =
            let uu____54319 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____54319
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____54360 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____54360;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = attrs
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term  in
                let uu____54441 =
                  let uu____54455 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____54455]  in
                let uu____54489 =
                  let uu____54500 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____54500
                   in
                FStar_Syntax_Util.arrow uu____54441 uu____54489
             in
          let l = FStar_Syntax_DsEnv.qualify env id1  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Parser_Const.exn_lid,
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
            let uu____54767 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____54767 with
            | FStar_Pervasives_Native.None  ->
                let uu____54782 =
                  let uu____54788 =
                    let uu____54790 =
                      let uu____54792 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____54792 " not found"  in
                    Prims.op_Hat "Effect name " uu____54790  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____54788)  in
                FStar_Errors.raise_error uu____54782
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____54828 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____54849 =
                  let uu____54852 =
                    let uu____54853 = desugar_term env t  in
                    ([], uu____54853)  in
                  FStar_Pervasives_Native.Some uu____54852  in
                (uu____54849, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____54894 =
                  let uu____54897 =
                    let uu____54898 = desugar_term env wp  in
                    ([], uu____54898)  in
                  FStar_Pervasives_Native.Some uu____54897  in
                let uu____54921 =
                  let uu____54924 =
                    let uu____54925 = desugar_term env t  in
                    ([], uu____54925)  in
                  FStar_Pervasives_Native.Some uu____54924  in
                (uu____54894, uu____54921)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____54956 =
                  let uu____54959 =
                    let uu____54960 = desugar_term env t  in
                    ([], uu____54960)  in
                  FStar_Pervasives_Native.Some uu____54959  in
                (FStar_Pervasives_Native.None, uu____54956)
             in
          (match uu____54828 with
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
            let uu____55062 =
              let uu____55063 =
                let uu____55078 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____55078, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____55063  in
            {
              FStar_Syntax_Syntax.sigel = uu____55062;
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
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____55152 =
        FStar_List.fold_left
          (fun uu____55187  ->
             fun d  ->
               match uu____55187 with
               | (env1,sigelts) ->
                   let uu____55232 = desugar_decl env1 d  in
                   (match uu____55232 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____55152 with
      | (env1,sigelts) ->
          let rec forward acc uu___31_55332 =
            match uu___31_55332 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____55391,FStar_Syntax_Syntax.Sig_let uu____55392) ->
                     let uu____55417 =
                       let uu____55425 =
                         let uu___3750_55436 = se2  in
                         let uu____55447 =
                           let uu____55454 =
                             FStar_List.filter
                               (fun uu___30_55476  ->
                                  match uu___30_55476 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____55485;
                                           FStar_Syntax_Syntax.vars =
                                             uu____55486;_},uu____55487);
                                      FStar_Syntax_Syntax.pos = uu____55488;
                                      FStar_Syntax_Syntax.vars = uu____55489;_}
                                      when
                                      let uu____55539 =
                                        let uu____55541 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____55541
                                         in
                                      uu____55539 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____55553 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____55454
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___3750_55436.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3750_55436.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3750_55436.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3750_55436.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____55447
                         }  in
                       uu____55425 :: se1 :: acc  in
                     forward uu____55417 sigelts1
                 | uu____55577 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____55605 = forward [] sigelts  in (env1, uu____55605)
  
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
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____55745) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____55765;
               FStar_Syntax_Syntax.exports = uu____55766;
               FStar_Syntax_Syntax.is_interface = uu____55767;_},FStar_Parser_AST.Module
             (current_lid,uu____55769)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____55816) ->
              let uu____55843 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____55843
           in
        let uu____55864 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____55942 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____55942, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____55991 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____55991, mname, decls, false)
           in
        match uu____55864 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____56068 = desugar_decls env2 decls  in
            (match uu____56068 with
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
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____56247 =
            (FStar_Options.interactive ()) &&
              (let uu____56250 =
                 let uu____56252 =
                   let uu____56254 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____56254  in
                 FStar_Util.get_file_extension uu____56252  in
               FStar_List.mem uu____56250 ["fsti"; "fsi"])
             in
          if uu____56247 then as_interface m else m  in
        let uu____56268 = desugar_modul_common curmod env m1  in
        match uu____56268 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____56330 = FStar_Syntax_DsEnv.pop ()  in
              (uu____56330, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____56384 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____56384 with
      | (env1,modul,pop_when_done) ->
          let uu____56441 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____56441 with
           | (env2,modul1) ->
               ((let uu____56485 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____56485
                 then
                   let uu____56488 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____56488
                 else ());
                (let uu____56493 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____56493, modul1))))
  
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
        (fun uu____56575  ->
           let uu____56576 = desugar_modul env modul  in
           match uu____56576 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____56669  ->
           let uu____56670 = desugar_decls env decls  in
           match uu____56670 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____56786  ->
             let uu____56787 = desugar_partial_modul modul env a_modul  in
             match uu____56787 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____57044 ->
                  let t =
                    let uu____57067 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____57067  in
                  let uu____57111 =
                    let uu____57112 = FStar_Syntax_Subst.compress t  in
                    uu____57112.FStar_Syntax_Syntax.n  in
                  (match uu____57111 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____57137,uu____57138)
                       -> bs1
                   | uu____57195 -> failwith "Impossible")
               in
            let uu____57210 =
              let uu____57221 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____57221
                FStar_Syntax_Syntax.t_unit
               in
            match uu____57210 with
            | (binders,uu____57243,binders_opening) ->
                let erase_term t =
                  let uu____57271 =
                    let uu____57280 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____57280  in
                  FStar_Syntax_Subst.close binders uu____57271  in
                let erase_tscheme uu____57318 =
                  match uu____57318 with
                  | (us,t) ->
                      let t1 =
                        let uu____57370 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____57370 t  in
                      let uu____57375 =
                        let uu____57384 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____57384  in
                      ([], uu____57375)
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
                    | uu____57465 ->
                        let bs =
                          let uu____57480 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____57480  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____57566 =
                          let uu____57567 =
                            let uu____57578 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____57578  in
                          uu____57567.FStar_Syntax_Syntax.n  in
                        (match uu____57566 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____57588,uu____57589) -> bs1
                         | uu____57646 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____57666 =
                      let uu____57675 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____57675  in
                    FStar_Syntax_Subst.close binders uu____57666  in
                  let uu___3909_57684 = action  in
                  let uu____57705 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____57714 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3909_57684.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3909_57684.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____57705;
                    FStar_Syntax_Syntax.action_typ = uu____57714
                  }  in
                let uu___3911_57725 = ed  in
                let uu____57766 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____57767 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____57776 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____57777 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____57778 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____57779 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____57780 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____57781 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____57782 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____57783 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____57784 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____57785 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____57786 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____57795 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____57796 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____57797 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3911_57725.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___3911_57725.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____57766;
                  FStar_Syntax_Syntax.signature = uu____57767;
                  FStar_Syntax_Syntax.ret_wp = uu____57776;
                  FStar_Syntax_Syntax.bind_wp = uu____57777;
                  FStar_Syntax_Syntax.if_then_else = uu____57778;
                  FStar_Syntax_Syntax.ite_wp = uu____57779;
                  FStar_Syntax_Syntax.stronger = uu____57780;
                  FStar_Syntax_Syntax.close_wp = uu____57781;
                  FStar_Syntax_Syntax.assert_p = uu____57782;
                  FStar_Syntax_Syntax.assume_p = uu____57783;
                  FStar_Syntax_Syntax.null_wp = uu____57784;
                  FStar_Syntax_Syntax.trivial = uu____57785;
                  FStar_Syntax_Syntax.repr = uu____57786;
                  FStar_Syntax_Syntax.return_repr = uu____57795;
                  FStar_Syntax_Syntax.bind_repr = uu____57796;
                  FStar_Syntax_Syntax.actions = uu____57797;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3911_57725.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3918_57885 = se  in
                  let uu____57896 =
                    let uu____57897 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____57897  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____57896;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3918_57885.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3918_57885.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3918_57885.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3918_57885.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___3924_57971 = se  in
                  let uu____57982 =
                    let uu____57983 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____57983
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____57982;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3924_57971.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3924_57971.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3924_57971.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3924_57971.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____58025 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____58026 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____58026 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____58043 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____58043
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____58050 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____58050)
  