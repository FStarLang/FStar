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
             (fun uu____104  ->
                match uu____104 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____159  ->
                             match uu____159 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____177 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____177 [] br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____183 =
                                     let uu____184 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____184]  in
                                   FStar_Syntax_Subst.close uu____183 branch1
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
      fun uu___61_241  ->
        match uu___61_241 with
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
  fun uu___62_261  ->
    match uu___62_261 with
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
  fun uu___63_279  ->
    match uu___63_279 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____282 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____290 .
    FStar_Parser_AST.imp ->
      'Auu____290 ->
        ('Auu____290 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____316 .
    FStar_Parser_AST.imp ->
      'Auu____316 ->
        ('Auu____316 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____335 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____356 -> true
            | uu____362 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____371 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____378 =
      let uu____379 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____379  in
    FStar_Parser_AST.mk_term uu____378 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____389 =
      let uu____390 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____390  in
    FStar_Parser_AST.mk_term uu____389 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____406 =
        let uu____407 = unparen t  in uu____407.FStar_Parser_AST.tm  in
      match uu____406 with
      | FStar_Parser_AST.Name l ->
          let uu____410 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____410 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____417) ->
          let uu____430 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____430 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____437,uu____438) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____443,uu____444) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____449,t1) -> is_comp_type env t1
      | uu____451 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____552;
                            FStar_Syntax_Syntax.vars = uu____553;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____581 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____581 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____597 =
                               let uu____598 =
                                 let uu____601 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____601  in
                               uu____598.FStar_Syntax_Syntax.n  in
                             match uu____597 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____624))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____631 -> msg
                           else msg  in
                         let uu____634 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____634
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____639 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____639 " is deprecated"  in
                         let uu____642 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____642
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____644 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____660 .
    'Auu____660 ->
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
        let uu____713 =
          let uu____716 =
            let uu____717 =
              let uu____723 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____723, r)  in
            FStar_Ident.mk_ident uu____717  in
          [uu____716]  in
        FStar_All.pipe_right uu____713 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____739 .
    env_t ->
      Prims.int ->
        'Auu____739 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____777 =
              let uu____778 =
                let uu____779 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____779 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____778 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____777  in
          let fallback uu____787 =
            let uu____788 = FStar_Ident.text_of_id op  in
            match uu____788 with
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
                let uu____809 = FStar_Options.ml_ish ()  in
                if uu____809
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
            | uu____834 -> FStar_Pervasives_Native.None  in
          let uu____836 =
            let uu____839 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___93_845 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___93_845.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___93_845.FStar_Syntax_Syntax.vars)
                 }) env true uu____839
             in
          match uu____836 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____850 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____865 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____865
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____914 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____918 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____918 with | (env1,uu____930) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____933,term) ->
          let uu____935 = free_type_vars env term  in (env, uu____935)
      | FStar_Parser_AST.TAnnotated (id1,uu____941) ->
          let uu____942 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____942 with | (env1,uu____954) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____958 = free_type_vars env t  in (env, uu____958)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____965 =
        let uu____966 = unparen t  in uu____966.FStar_Parser_AST.tm  in
      match uu____965 with
      | FStar_Parser_AST.Labeled uu____969 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____982 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____982 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____987 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____990 -> []
      | FStar_Parser_AST.Uvar uu____991 -> []
      | FStar_Parser_AST.Var uu____992 -> []
      | FStar_Parser_AST.Projector uu____993 -> []
      | FStar_Parser_AST.Discrim uu____998 -> []
      | FStar_Parser_AST.Name uu____999 -> []
      | FStar_Parser_AST.Requires (t1,uu____1001) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____1009) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____1016,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____1035,ts) ->
          FStar_List.collect
            (fun uu____1056  ->
               match uu____1056 with
               | (t1,uu____1064) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____1065,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____1073) ->
          let uu____1074 = free_type_vars env t1  in
          let uu____1077 = free_type_vars env t2  in
          FStar_List.append uu____1074 uu____1077
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____1082 = free_type_vars_b env b  in
          (match uu____1082 with
           | (env1,f) ->
               let uu____1097 = free_type_vars env1 t1  in
               FStar_List.append f uu____1097)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1114 =
            FStar_List.fold_left
              (fun uu____1138  ->
                 fun bt  ->
                   match uu____1138 with
                   | (env1,free) ->
                       let uu____1162 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1177 = free_type_vars env1 body  in
                             (env1, uu____1177)
                          in
                       (match uu____1162 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1114 with
           | (env1,free) ->
               let uu____1206 = free_type_vars env1 body  in
               FStar_List.append free uu____1206)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1215 =
            FStar_List.fold_left
              (fun uu____1235  ->
                 fun binder  ->
                   match uu____1235 with
                   | (env1,free) ->
                       let uu____1255 = free_type_vars_b env1 binder  in
                       (match uu____1255 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1215 with
           | (env1,free) ->
               let uu____1286 = free_type_vars env1 body  in
               FStar_List.append free uu____1286)
      | FStar_Parser_AST.Project (t1,uu____1290) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____1301 = free_type_vars env rel  in
          let uu____1304 =
            let uu____1307 = free_type_vars env init1  in
            let uu____1310 =
              FStar_List.collect
                (fun uu____1319  ->
                   match uu____1319 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1325 = free_type_vars env rel1  in
                       let uu____1328 =
                         let uu____1331 = free_type_vars env just  in
                         let uu____1334 = free_type_vars env next  in
                         FStar_List.append uu____1331 uu____1334  in
                       FStar_List.append uu____1325 uu____1328) steps
               in
            FStar_List.append uu____1307 uu____1310  in
          FStar_List.append uu____1301 uu____1304
      | FStar_Parser_AST.Abs uu____1337 -> []
      | FStar_Parser_AST.Let uu____1344 -> []
      | FStar_Parser_AST.LetOpen uu____1365 -> []
      | FStar_Parser_AST.If uu____1370 -> []
      | FStar_Parser_AST.QForall uu____1377 -> []
      | FStar_Parser_AST.QExists uu____1390 -> []
      | FStar_Parser_AST.Record uu____1403 -> []
      | FStar_Parser_AST.Match uu____1416 -> []
      | FStar_Parser_AST.TryWith uu____1431 -> []
      | FStar_Parser_AST.Bind uu____1446 -> []
      | FStar_Parser_AST.Quote uu____1453 -> []
      | FStar_Parser_AST.VQuote uu____1458 -> []
      | FStar_Parser_AST.Antiquote uu____1459 -> []
      | FStar_Parser_AST.Seq uu____1460 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1514 =
        let uu____1515 = unparen t1  in uu____1515.FStar_Parser_AST.tm  in
      match uu____1514 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1557 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1582 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1582  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1604 =
                     let uu____1605 =
                       let uu____1610 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1610)  in
                     FStar_Parser_AST.TAnnotated uu____1605  in
                   FStar_Parser_AST.mk_binder uu____1604
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
        let uu____1628 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1628  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1650 =
                     let uu____1651 =
                       let uu____1656 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1656)  in
                     FStar_Parser_AST.TAnnotated uu____1651  in
                   FStar_Parser_AST.mk_binder uu____1650
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1658 =
             let uu____1659 = unparen t  in uu____1659.FStar_Parser_AST.tm
              in
           match uu____1658 with
           | FStar_Parser_AST.Product uu____1660 -> t
           | uu____1667 ->
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
      | uu____1704 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1715 -> true
    | FStar_Parser_AST.PatTvar (uu____1719,uu____1720) -> true
    | FStar_Parser_AST.PatVar (uu____1726,uu____1727) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1734) -> is_var_pattern p1
    | uu____1747 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1758) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1771;
           FStar_Parser_AST.prange = uu____1772;_},uu____1773)
        -> true
    | uu____1785 -> false
  
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
    | uu____1801 -> p
  
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
            let uu____1874 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1874 with
             | (name,args,uu____1917) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1967);
               FStar_Parser_AST.prange = uu____1968;_},args)
            when is_top_level1 ->
            let uu____1978 =
              let uu____1983 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1983  in
            (uu____1978, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____2005);
               FStar_Parser_AST.prange = uu____2006;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____2036 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____2095 -> acc
        | FStar_Parser_AST.PatName uu____2098 -> acc
        | FStar_Parser_AST.PatOp uu____2099 -> acc
        | FStar_Parser_AST.PatConst uu____2100 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____2117) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____2123) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____2132) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____2149 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____2149
        | FStar_Parser_AST.PatAscribed (pat,uu____2157) ->
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
    match projectee with | LocalBinder _0 -> true | uu____2239 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2281 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___64_2330  ->
    match uu___64_2330 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2337 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2370  ->
    match uu____2370 with
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
      let uu____2452 =
        let uu____2469 =
          let uu____2472 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2472  in
        let uu____2473 =
          let uu____2484 =
            let uu____2493 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2493)  in
          [uu____2484]  in
        (uu____2469, uu____2473)  in
      FStar_Syntax_Syntax.Tm_app uu____2452  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2542 =
        let uu____2559 =
          let uu____2562 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2562  in
        let uu____2563 =
          let uu____2574 =
            let uu____2583 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2583)  in
          [uu____2574]  in
        (uu____2559, uu____2563)  in
      FStar_Syntax_Syntax.Tm_app uu____2542  in
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
          let uu____2646 =
            let uu____2663 =
              let uu____2666 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2666  in
            let uu____2667 =
              let uu____2678 =
                let uu____2687 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2687)  in
              let uu____2695 =
                let uu____2706 =
                  let uu____2715 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2715)  in
                [uu____2706]  in
              uu____2678 :: uu____2695  in
            (uu____2663, uu____2667)  in
          FStar_Syntax_Syntax.Tm_app uu____2646  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2775 =
        let uu____2790 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2809  ->
               match uu____2809 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2820;
                    FStar_Syntax_Syntax.index = uu____2821;
                    FStar_Syntax_Syntax.sort = t;_},uu____2823)
                   ->
                   let uu____2831 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2831) uu____2790
         in
      FStar_All.pipe_right bs uu____2775  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2847 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2865 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2893 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2914,uu____2915,bs,t,uu____2918,uu____2919)
                            ->
                            let uu____2928 = bs_univnames bs  in
                            let uu____2931 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2928 uu____2931
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2934,uu____2935,t,uu____2937,uu____2938,uu____2939)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2946 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2893 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___94_2955 = s  in
        let uu____2956 =
          let uu____2957 =
            let uu____2966 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2984,bs,t,lids1,lids2) ->
                          let uu___95_2997 = se  in
                          let uu____2998 =
                            let uu____2999 =
                              let uu____3016 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3017 =
                                let uu____3018 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3018 t  in
                              (lid, uvs, uu____3016, uu____3017, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2999
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2998;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___95_2997.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___95_2997.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___95_2997.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___95_2997.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3032,t,tlid,n1,lids1) ->
                          let uu___96_3043 = se  in
                          let uu____3044 =
                            let uu____3045 =
                              let uu____3061 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3061, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3045  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3044;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___96_3043.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___96_3043.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___96_3043.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___96_3043.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____3065 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2966, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2957  in
        {
          FStar_Syntax_Syntax.sigel = uu____2956;
          FStar_Syntax_Syntax.sigrng =
            (uu___94_2955.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___94_2955.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___94_2955.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___94_2955.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3072,t) ->
        let uvs =
          let uu____3075 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3075 FStar_Util.set_elements  in
        let uu___97_3080 = s  in
        let uu____3081 =
          let uu____3082 =
            let uu____3089 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3089)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3082  in
        {
          FStar_Syntax_Syntax.sigel = uu____3081;
          FStar_Syntax_Syntax.sigrng =
            (uu___97_3080.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___97_3080.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___97_3080.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___97_3080.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3113 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3116 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3123) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3156,(FStar_Util.Inl t,uu____3158),uu____3159)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3206,(FStar_Util.Inr c,uu____3208),uu____3209)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3256 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3257,(FStar_Util.Inl t,uu____3259),uu____3260) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3307,(FStar_Util.Inr c,uu____3309),uu____3310) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3357 -> empty_set  in
          FStar_Util.set_union uu____3113 uu____3116  in
        let all_lb_univs =
          let uu____3361 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3377 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3377) empty_set)
             in
          FStar_All.pipe_right uu____3361 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___98_3387 = s  in
        let uu____3388 =
          let uu____3389 =
            let uu____3396 =
              let uu____3397 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___99_3409 = lb  in
                        let uu____3410 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3413 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___99_3409.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3410;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___99_3409.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3413;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___99_3409.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___99_3409.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3397)  in
            (uu____3396, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3389  in
        {
          FStar_Syntax_Syntax.sigel = uu____3388;
          FStar_Syntax_Syntax.sigrng =
            (uu___98_3387.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___98_3387.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___98_3387.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___98_3387.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3422,fml) ->
        let uvs =
          let uu____3425 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3425 FStar_Util.set_elements  in
        let uu___100_3430 = s  in
        let uu____3431 =
          let uu____3432 =
            let uu____3439 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3439)  in
          FStar_Syntax_Syntax.Sig_assume uu____3432  in
        {
          FStar_Syntax_Syntax.sigel = uu____3431;
          FStar_Syntax_Syntax.sigrng =
            (uu___100_3430.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___100_3430.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___100_3430.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___100_3430.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3441,bs,c,flags1) ->
        let uvs =
          let uu____3450 =
            let uu____3453 = bs_univnames bs  in
            let uu____3456 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3453 uu____3456  in
          FStar_All.pipe_right uu____3450 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___101_3464 = s  in
        let uu____3465 =
          let uu____3466 =
            let uu____3479 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3480 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3479, uu____3480, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3466  in
        {
          FStar_Syntax_Syntax.sigel = uu____3465;
          FStar_Syntax_Syntax.sigrng =
            (uu___101_3464.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___101_3464.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___101_3464.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___101_3464.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3483 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___65_3491  ->
    match uu___65_3491 with
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
    | uu____3542 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3563 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3563)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3589 =
      let uu____3590 = unparen t  in uu____3590.FStar_Parser_AST.tm  in
    match uu____3589 with
    | FStar_Parser_AST.Wild  ->
        let uu____3596 =
          let uu____3597 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3597  in
        FStar_Util.Inr uu____3596
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3610)) ->
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
             let uu____3701 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3701
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3718 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3718
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3734 =
               let uu____3740 =
                 let uu____3742 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3742
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3740)
                in
             FStar_Errors.raise_error uu____3734 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3751 ->
        let rec aux t1 univargs =
          let uu____3788 =
            let uu____3789 = unparen t1  in uu____3789.FStar_Parser_AST.tm
             in
          match uu____3788 with
          | FStar_Parser_AST.App (t2,targ,uu____3797) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___66_3824  ->
                     match uu___66_3824 with
                     | FStar_Util.Inr uu____3831 -> true
                     | uu____3834 -> false) univargs
              then
                let uu____3842 =
                  let uu____3843 =
                    FStar_List.map
                      (fun uu___67_3853  ->
                         match uu___67_3853 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3843  in
                FStar_Util.Inr uu____3842
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___68_3879  ->
                        match uu___68_3879 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3889 -> failwith "impossible")
                     univargs
                    in
                 let uu____3893 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3893)
          | uu____3909 ->
              let uu____3910 =
                let uu____3916 =
                  let uu____3918 =
                    let uu____3920 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3920 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3918  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3916)  in
              FStar_Errors.raise_error uu____3910 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3935 ->
        let uu____3936 =
          let uu____3942 =
            let uu____3944 =
              let uu____3946 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3946 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3944  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3942)  in
        FStar_Errors.raise_error uu____3936 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3987;_});
            FStar_Syntax_Syntax.pos = uu____3988;
            FStar_Syntax_Syntax.vars = uu____3989;_})::uu____3990
        ->
        let uu____4021 =
          let uu____4027 =
            let uu____4029 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4029
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4027)  in
        FStar_Errors.raise_error uu____4021 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4035 ->
        let uu____4054 =
          let uu____4060 =
            let uu____4062 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4062
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4060)  in
        FStar_Errors.raise_error uu____4054 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4075 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4075) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4103 = FStar_List.hd fields  in
        match uu____4103 with
        | (f,uu____4113) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4125 =
                match uu____4125 with
                | (f',uu____4131) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4133 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4133
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
              (let uu____4143 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4143);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____4506 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4513 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4514 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4516,pats1) ->
              let aux out uu____4557 =
                match uu____4557 with
                | (p2,uu____4570) ->
                    let intersection =
                      let uu____4580 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4580 out  in
                    let uu____4583 = FStar_Util.set_is_empty intersection  in
                    if uu____4583
                    then
                      let uu____4588 = pat_vars p2  in
                      FStar_Util.set_union out uu____4588
                    else
                      (let duplicate_bv =
                         let uu____4594 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4594  in
                       let uu____4597 =
                         let uu____4603 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4603)
                          in
                       FStar_Errors.raise_error uu____4597 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4627 = pat_vars p1  in
            FStar_All.pipe_right uu____4627 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4655 =
                let uu____4657 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4657  in
              if uu____4655
              then ()
              else
                (let nonlinear_vars =
                   let uu____4666 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4666  in
                 let first_nonlinear_var =
                   let uu____4670 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4670  in
                 let uu____4673 =
                   let uu____4679 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4679)  in
                 FStar_Errors.raise_error uu____4673 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4707 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4707 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4724 ->
            let uu____4727 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4727 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4878 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4902 =
              let uu____4903 =
                let uu____4904 =
                  let uu____4911 =
                    let uu____4912 =
                      let uu____4918 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4918, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4912  in
                  (uu____4911, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4904  in
              {
                FStar_Parser_AST.pat = uu____4903;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4902
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4938 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4941 = aux loc env1 p2  in
              match uu____4941 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___102_5030 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___103_5035 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___103_5035.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___103_5035.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___102_5030.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___104_5037 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___105_5042 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___105_5042.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___105_5042.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___104_5037.FStar_Syntax_Syntax.p)
                        }
                    | uu____5043 when top -> p4
                    | uu____5044 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____5049 =
                    match binder with
                    | LetBinder uu____5070 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____5095 = close_fun env1 t  in
                          desugar_term env1 uu____5095  in
                        let x1 =
                          let uu___106_5097 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___106_5097.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___106_5097.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____5049 with
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
            let uu____5165 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____5165, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5179 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5179, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5203 = resolvex loc env1 x  in
            (match uu____5203 with
             | (loc1,env2,xbv) ->
                 let uu____5232 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5232, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5255 = resolvex loc env1 x  in
            (match uu____5255 with
             | (loc1,env2,xbv) ->
                 let uu____5284 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5284, [], imp))
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
            let uu____5299 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5299, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5329;_},args)
            ->
            let uu____5335 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5396  ->
                     match uu____5396 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5477 = aux loc1 env2 arg  in
                         (match uu____5477 with
                          | (loc2,env3,uu____5524,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5335 with
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
                 let uu____5656 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5656, annots, false))
        | FStar_Parser_AST.PatApp uu____5674 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5705 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5756  ->
                     match uu____5756 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5817 = aux loc1 env2 pat  in
                         (match uu____5817 with
                          | (loc2,env3,uu____5859,pat1,ans,uu____5862) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5705 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5959 =
                     let uu____5962 =
                       let uu____5969 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5969  in
                     let uu____5970 =
                       let uu____5971 =
                         let uu____5985 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5985, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5971  in
                     FStar_All.pipe_left uu____5962 uu____5970  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____6019 =
                            let uu____6020 =
                              let uu____6034 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____6034, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____6020  in
                          FStar_All.pipe_left (pos_r r) uu____6019) pats1
                     uu____5959
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
            let uu____6092 =
              FStar_List.fold_left
                (fun uu____6152  ->
                   fun p2  ->
                     match uu____6152 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6234 = aux loc1 env2 p2  in
                         (match uu____6234 with
                          | (loc2,env3,uu____6281,pat,ans,uu____6284) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____6092 with
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
                   | uu____6450 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6453 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6453, annots, false))
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
                   (fun uu____6534  ->
                      match uu____6534 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6564  ->
                      match uu____6564 with
                      | (f,uu____6570) ->
                          let uu____6571 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6597  ->
                                    match uu____6597 with
                                    | (g,uu____6604) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6571 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6610,p2) ->
                               p2)))
               in
            let app =
              let uu____6617 =
                let uu____6618 =
                  let uu____6625 =
                    let uu____6626 =
                      let uu____6627 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6627  in
                    FStar_Parser_AST.mk_pattern uu____6626
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6625, args)  in
                FStar_Parser_AST.PatApp uu____6618  in
              FStar_Parser_AST.mk_pattern uu____6617
                p1.FStar_Parser_AST.prange
               in
            let uu____6630 = aux loc env1 app  in
            (match uu____6630 with
             | (env2,e,b,p2,annots,uu____6676) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6716 =
                         let uu____6717 =
                           let uu____6731 =
                             let uu___107_6732 = fv  in
                             let uu____6733 =
                               let uu____6736 =
                                 let uu____6737 =
                                   let uu____6744 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6744)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6737
                                  in
                               FStar_Pervasives_Native.Some uu____6736  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___107_6732.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___107_6732.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6733
                             }  in
                           (uu____6731, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6717  in
                       FStar_All.pipe_left pos uu____6716
                   | uu____6770 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6856 = aux' true loc env1 p2  in
            (match uu____6856 with
             | (loc1,env2,var,p3,ans,uu____6900) ->
                 let uu____6915 =
                   FStar_List.fold_left
                     (fun uu____6964  ->
                        fun p4  ->
                          match uu____6964 with
                          | (loc2,env3,ps1) ->
                              let uu____7029 = aux' true loc2 env3 p4  in
                              (match uu____7029 with
                               | (loc3,env4,uu____7070,p5,ans1,uu____7073) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6915 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7234 ->
            let uu____7235 = aux' true loc env1 p1  in
            (match uu____7235 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7332 = aux_maybe_or env p  in
      match uu____7332 with
      | (env1,b,pats) ->
          ((let uu____7387 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7387
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
          let uu____7460 =
            let uu____7461 =
              let uu____7472 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7472, (ty, tacopt))  in
            LetBinder uu____7461  in
          (env, uu____7460, [])  in
        let op_to_ident x =
          let uu____7489 =
            let uu____7495 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____7495, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7489  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7517 = op_to_ident x  in
              mklet uu____7517 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7519) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7525;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7541 = op_to_ident x  in
              let uu____7542 = desugar_term env t  in
              mklet uu____7541 uu____7542 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7544);
                 FStar_Parser_AST.prange = uu____7545;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7565 = desugar_term env t  in
              mklet x uu____7565 tacopt1
          | uu____7566 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7579 = desugar_data_pat env p  in
           match uu____7579 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7608;
                      FStar_Syntax_Syntax.p = uu____7609;_},uu____7610)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7623;
                      FStar_Syntax_Syntax.p = uu____7624;_},uu____7625)::[]
                     -> []
                 | uu____7638 -> p1  in
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
  fun uu____7646  ->
    fun env  ->
      fun pat  ->
        let uu____7650 = desugar_data_pat env pat  in
        match uu____7650 with | (env1,uu____7666,pat1) -> (env1, pat1)

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
      let uu____7688 = desugar_term_aq env e  in
      match uu____7688 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7707 = desugar_typ_aq env e  in
      match uu____7707 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7717  ->
        fun range  ->
          match uu____7717 with
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
              ((let uu____7739 =
                  let uu____7741 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7741  in
                if uu____7739
                then
                  let uu____7744 =
                    let uu____7750 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7750)  in
                  FStar_Errors.log_issue range uu____7744
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
                  let uu____7771 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7771 range  in
                let lid1 =
                  let uu____7775 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7775 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7785 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7785 range  in
                           let private_fv =
                             let uu____7787 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7787 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___108_7788 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___108_7788.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___108_7788.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7789 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7793 =
                        let uu____7799 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7799)
                         in
                      FStar_Errors.raise_error uu____7793 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7819 =
                  let uu____7826 =
                    let uu____7827 =
                      let uu____7844 =
                        let uu____7855 =
                          let uu____7864 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7864)  in
                        [uu____7855]  in
                      (lid1, uu____7844)  in
                    FStar_Syntax_Syntax.Tm_app uu____7827  in
                  FStar_Syntax_Syntax.mk uu____7826  in
                uu____7819 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7915 =
          let uu____7916 = unparen t  in uu____7916.FStar_Parser_AST.tm  in
        match uu____7915 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7917; FStar_Ident.ident = uu____7918;
              FStar_Ident.nsstr = uu____7919; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7924 ->
            let uu____7925 =
              let uu____7931 =
                let uu____7933 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____7933  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7931)  in
            FStar_Errors.raise_error uu____7925 t.FStar_Parser_AST.range
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
          let uu___109_8020 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___109_8020.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___109_8020.FStar_Syntax_Syntax.vars)
          }  in
        let uu____8023 =
          let uu____8024 = unparen top  in uu____8024.FStar_Parser_AST.tm  in
        match uu____8023 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____8029 ->
            let uu____8038 = desugar_formula env top  in (uu____8038, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____8047 = desugar_formula env t  in (uu____8047, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8056 = desugar_formula env t  in (uu____8056, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8083 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8083, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8085 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8085, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8094 =
                let uu____8095 =
                  let uu____8102 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8102, args)  in
                FStar_Parser_AST.Op uu____8095  in
              FStar_Parser_AST.mk_term uu____8094 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8107 =
              let uu____8108 =
                let uu____8109 =
                  let uu____8116 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8116, [e])  in
                FStar_Parser_AST.Op uu____8109  in
              FStar_Parser_AST.mk_term uu____8108 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8107
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8128 = FStar_Ident.text_of_id op_star  in
             uu____8128 = "*") &&
              (let uu____8133 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____8133 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8150;_},t1::t2::[])
                  when
                  let uu____8156 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8156 FStar_Option.isNone ->
                  let uu____8163 = flatten1 t1  in
                  FStar_List.append uu____8163 [t2]
              | uu____8166 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___110_8171 = top  in
              let uu____8172 =
                let uu____8173 =
                  let uu____8184 =
                    FStar_List.map (fun _0_1  -> FStar_Util.Inr _0_1) terms
                     in
                  (uu____8184, rhs)  in
                FStar_Parser_AST.Sum uu____8173  in
              {
                FStar_Parser_AST.tm = uu____8172;
                FStar_Parser_AST.range =
                  (uu___110_8171.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___110_8171.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8202 =
              let uu____8203 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8203  in
            (uu____8202, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8209 =
              let uu____8215 =
                let uu____8217 =
                  let uu____8219 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8219 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8217  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8215)  in
            FStar_Errors.raise_error uu____8209 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8234 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8234 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8241 =
                   let uu____8247 =
                     let uu____8249 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8249
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8247)
                    in
                 FStar_Errors.raise_error uu____8241
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____8264 =
                     let uu____8289 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8351 = desugar_term_aq env t  in
                               match uu____8351 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8289 FStar_List.unzip  in
                   (match uu____8264 with
                    | (args1,aqs) ->
                        let uu____8484 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8484, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8501)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8518 =
              let uu___111_8519 = top  in
              let uu____8520 =
                let uu____8521 =
                  let uu____8528 =
                    let uu___112_8529 = top  in
                    let uu____8530 =
                      let uu____8531 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8531  in
                    {
                      FStar_Parser_AST.tm = uu____8530;
                      FStar_Parser_AST.range =
                        (uu___112_8529.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___112_8529.FStar_Parser_AST.level)
                    }  in
                  (uu____8528, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8521  in
              {
                FStar_Parser_AST.tm = uu____8520;
                FStar_Parser_AST.range =
                  (uu___111_8519.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___111_8519.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8518
        | FStar_Parser_AST.Construct (n1,(a,uu____8539)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8559 =
                let uu___113_8560 = top  in
                let uu____8561 =
                  let uu____8562 =
                    let uu____8569 =
                      let uu___114_8570 = top  in
                      let uu____8571 =
                        let uu____8572 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8572  in
                      {
                        FStar_Parser_AST.tm = uu____8571;
                        FStar_Parser_AST.range =
                          (uu___114_8570.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___114_8570.FStar_Parser_AST.level)
                      }  in
                    (uu____8569, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8562  in
                {
                  FStar_Parser_AST.tm = uu____8561;
                  FStar_Parser_AST.range =
                    (uu___113_8560.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___113_8560.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8559))
        | FStar_Parser_AST.Construct (n1,(a,uu____8580)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8597 =
              let uu___115_8598 = top  in
              let uu____8599 =
                let uu____8600 =
                  let uu____8607 =
                    let uu___116_8608 = top  in
                    let uu____8609 =
                      let uu____8610 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8610  in
                    {
                      FStar_Parser_AST.tm = uu____8609;
                      FStar_Parser_AST.range =
                        (uu___116_8608.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___116_8608.FStar_Parser_AST.level)
                    }  in
                  (uu____8607, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8600  in
              {
                FStar_Parser_AST.tm = uu____8599;
                FStar_Parser_AST.range =
                  (uu___115_8598.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___115_8598.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8597
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8616; FStar_Ident.ident = uu____8617;
              FStar_Ident.nsstr = uu____8618; FStar_Ident.str = "Type0";_}
            ->
            let uu____8623 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8623, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8624; FStar_Ident.ident = uu____8625;
              FStar_Ident.nsstr = uu____8626; FStar_Ident.str = "Type";_}
            ->
            let uu____8631 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8631, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8632; FStar_Ident.ident = uu____8633;
               FStar_Ident.nsstr = uu____8634; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8654 =
              let uu____8655 =
                let uu____8656 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8656  in
              mk1 uu____8655  in
            (uu____8654, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8657; FStar_Ident.ident = uu____8658;
              FStar_Ident.nsstr = uu____8659; FStar_Ident.str = "Effect";_}
            ->
            let uu____8664 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8664, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8665; FStar_Ident.ident = uu____8666;
              FStar_Ident.nsstr = uu____8667; FStar_Ident.str = "True";_}
            ->
            let uu____8672 =
              let uu____8673 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8673
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8672, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8674; FStar_Ident.ident = uu____8675;
              FStar_Ident.nsstr = uu____8676; FStar_Ident.str = "False";_}
            ->
            let uu____8681 =
              let uu____8682 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8682
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8681, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8685;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8688 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8688 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8697 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8697, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8699 =
                    let uu____8701 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8701 txt
                     in
                  failwith uu____8699))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8710 = desugar_name mk1 setpos env true l  in
              (uu____8710, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8719 = desugar_name mk1 setpos env true l  in
              (uu____8719, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8737 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8737 with
                | FStar_Pervasives_Native.Some uu____8747 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8755 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8755 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8773 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8794 =
                    let uu____8795 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8795  in
                  (uu____8794, noaqs)
              | uu____8801 ->
                  let uu____8809 =
                    let uu____8815 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8815)  in
                  FStar_Errors.raise_error uu____8809
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8825 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8825 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8832 =
                    let uu____8838 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8838)
                     in
                  FStar_Errors.raise_error uu____8832
                    top.FStar_Parser_AST.range
              | uu____8846 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8850 = desugar_name mk1 setpos env true lid'  in
                  (uu____8850, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8872 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8872 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8891 ->
                       let uu____8898 =
                         FStar_Util.take
                           (fun uu____8922  ->
                              match uu____8922 with
                              | (uu____8928,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8898 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8973 =
                              let uu____8998 =
                                FStar_List.map
                                  (fun uu____9041  ->
                                     match uu____9041 with
                                     | (t,imp) ->
                                         let uu____9058 =
                                           desugar_term_aq env t  in
                                         (match uu____9058 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8998
                                FStar_List.unzip
                               in
                            (match uu____8973 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9201 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9201, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9220 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9220 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9231 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___69_9259  ->
                 match uu___69_9259 with
                 | FStar_Util.Inr uu____9265 -> true
                 | uu____9267 -> false) binders
            ->
            let terms =
              let uu____9276 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___70_9293  ->
                        match uu___70_9293 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9299 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9276 [t]  in
            let uu____9301 =
              let uu____9326 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9383 = desugar_typ_aq env t1  in
                        match uu____9383 with
                        | (t',aq) ->
                            let uu____9394 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9394, aq)))
                 in
              FStar_All.pipe_right uu____9326 FStar_List.unzip  in
            (match uu____9301 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9504 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9504
                    in
                 let uu____9513 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9513, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9540 =
              let uu____9557 =
                let uu____9564 =
                  let uu____9571 =
                    FStar_All.pipe_left (fun _0_2  -> FStar_Util.Inl _0_2)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9571]  in
                FStar_List.append binders uu____9564  in
              FStar_List.fold_left
                (fun uu____9624  ->
                   fun b  ->
                     match uu____9624 with
                     | (env1,tparams,typs) ->
                         let uu____9685 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9700 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9700)
                            in
                         (match uu____9685 with
                          | (xopt,t1) ->
                              let uu____9725 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9734 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9734)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9725 with
                               | (env2,x) ->
                                   let uu____9754 =
                                     let uu____9757 =
                                       let uu____9760 =
                                         let uu____9761 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9761
                                          in
                                       [uu____9760]  in
                                     FStar_List.append typs uu____9757  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___117_9787 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___117_9787.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___117_9787.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9754)))) (env, [], []) uu____9557
               in
            (match uu____9540 with
             | (env1,uu____9815,targs) ->
                 let tup =
                   let uu____9838 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9838
                    in
                 let uu____9839 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9839, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9858 = uncurry binders t  in
            (match uu____9858 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___71_9902 =
                   match uu___71_9902 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9919 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9919
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9943 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9943 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9976 = aux env [] bs  in (uu____9976, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9985 = desugar_binder env b  in
            (match uu____9985 with
             | (FStar_Pervasives_Native.None ,uu____9996) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____10011 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____10011 with
                  | ((x,uu____10027),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____10040 =
                        let uu____10041 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____10041  in
                      (uu____10040, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10120 = FStar_Util.set_is_empty i  in
                    if uu____10120
                    then
                      let uu____10125 = FStar_Util.set_union acc set1  in
                      aux uu____10125 sets2
                    else
                      (let uu____10130 =
                         let uu____10131 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10131  in
                       FStar_Pervasives_Native.Some uu____10130)
                 in
              let uu____10134 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10134 sets  in
            ((let uu____10138 = check_disjoint bvss  in
              match uu____10138 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10142 =
                    let uu____10148 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10148)
                     in
                  let uu____10152 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10142 uu____10152);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10160 =
                FStar_List.fold_left
                  (fun uu____10180  ->
                     fun pat  ->
                       match uu____10180 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10206,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10216 =
                                  let uu____10219 = free_type_vars env1 t  in
                                  FStar_List.append uu____10219 ftvs  in
                                (env1, uu____10216)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10224,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10235 =
                                  let uu____10238 = free_type_vars env1 t  in
                                  let uu____10241 =
                                    let uu____10244 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10244 ftvs  in
                                  FStar_List.append uu____10238 uu____10241
                                   in
                                (env1, uu____10235)
                            | uu____10249 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10160 with
              | (uu____10258,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10270 =
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
                    FStar_List.append uu____10270 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___72_10327 =
                    match uu___72_10327 with
                    | [] ->
                        let uu____10354 = desugar_term_aq env1 body  in
                        (match uu____10354 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10391 =
                                       let uu____10392 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10392
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10391
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
                             let uu____10461 =
                               let uu____10464 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10464  in
                             (uu____10461, aq))
                    | p::rest ->
                        let uu____10479 = desugar_binding_pat env1 p  in
                        (match uu____10479 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10513)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10528 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10537 =
                               match b with
                               | LetBinder uu____10578 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10647) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10701 =
                                           let uu____10710 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10710, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10701
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10772,uu____10773) ->
                                              let tup2 =
                                                let uu____10775 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10775
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10780 =
                                                  let uu____10787 =
                                                    let uu____10788 =
                                                      let uu____10805 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10808 =
                                                        let uu____10819 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10828 =
                                                          let uu____10839 =
                                                            let uu____10848 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10848
                                                             in
                                                          [uu____10839]  in
                                                        uu____10819 ::
                                                          uu____10828
                                                         in
                                                      (uu____10805,
                                                        uu____10808)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10788
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10787
                                                   in
                                                uu____10780
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10899 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10899
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10950,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10952,pats)) ->
                                              let tupn =
                                                let uu____10997 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10997
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____11010 =
                                                  let uu____11011 =
                                                    let uu____11028 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____11031 =
                                                      let uu____11042 =
                                                        let uu____11053 =
                                                          let uu____11062 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____11062
                                                           in
                                                        [uu____11053]  in
                                                      FStar_List.append args
                                                        uu____11042
                                                       in
                                                    (uu____11028,
                                                      uu____11031)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11011
                                                   in
                                                mk1 uu____11010  in
                                              let p2 =
                                                let uu____11110 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11110
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11157 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10537 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11251,uu____11252,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11274 =
                let uu____11275 = unparen e  in
                uu____11275.FStar_Parser_AST.tm  in
              match uu____11274 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11285 ->
                  let uu____11286 = desugar_term_aq env e  in
                  (match uu____11286 with
                   | (head1,aq) ->
                       let uu____11299 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11299, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11306 ->
            let rec aux args aqs e =
              let uu____11383 =
                let uu____11384 = unparen e  in
                uu____11384.FStar_Parser_AST.tm  in
              match uu____11383 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11402 = desugar_term_aq env t  in
                  (match uu____11402 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11450 ->
                  let uu____11451 = desugar_term_aq env e  in
                  (match uu____11451 with
                   | (head1,aq) ->
                       let uu____11472 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11472, (join_aqs (aq :: aqs))))
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
            let uu____11535 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11535
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
            let uu____11587 = desugar_term_aq env t  in
            (match uu____11587 with
             | (tm,s) ->
                 let uu____11598 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11598, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11604 =
              let uu____11617 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11617 then desugar_typ_aq else desugar_term_aq  in
            uu____11604 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11676 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11819  ->
                        match uu____11819 with
                        | (attr_opt,(p,def)) ->
                            let uu____11877 = is_app_pattern p  in
                            if uu____11877
                            then
                              let uu____11910 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11910, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11993 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11993, def1)
                               | uu____12038 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12076);
                                           FStar_Parser_AST.prange =
                                             uu____12077;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12126 =
                                            let uu____12147 =
                                              let uu____12152 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12152  in
                                            (uu____12147, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12126, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12244) ->
                                        if top_level
                                        then
                                          let uu____12280 =
                                            let uu____12301 =
                                              let uu____12306 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12306  in
                                            (uu____12301, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12280, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12397 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12430 =
                FStar_List.fold_left
                  (fun uu____12503  ->
                     fun uu____12504  ->
                       match (uu____12503, uu____12504) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12612,uu____12613),uu____12614))
                           ->
                           let uu____12731 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12757 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12757 with
                                  | (env2,xx) ->
                                      let uu____12776 =
                                        let uu____12779 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12779 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12776))
                             | FStar_Util.Inr l ->
                                 let uu____12787 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12787, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12731 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12430 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12935 =
                    match uu____12935 with
                    | (attrs_opt,(uu____12971,args,result_t),def) ->
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
                                let uu____13059 = is_comp_type env1 t  in
                                if uu____13059
                                then
                                  ((let uu____13063 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13073 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13073))
                                       in
                                    match uu____13063 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13080 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13083 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13083))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____13080
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
                          | uu____13094 ->
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
                              let uu____13109 =
                                let uu____13110 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13110
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13109
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
                  let uu____13191 = desugar_term_aq env' body  in
                  (match uu____13191 with
                   | (body1,aq) ->
                       let uu____13204 =
                         let uu____13207 =
                           let uu____13208 =
                             let uu____13222 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13222)  in
                           FStar_Syntax_Syntax.Tm_let uu____13208  in
                         FStar_All.pipe_left mk1 uu____13207  in
                       (uu____13204, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13297 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13297 with
              | (env1,binder,pat1) ->
                  let uu____13319 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13345 = desugar_term_aq env1 t2  in
                        (match uu____13345 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13359 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13359
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13360 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13360, aq))
                    | LocalBinder (x,uu____13393) ->
                        let uu____13394 = desugar_term_aq env1 t2  in
                        (match uu____13394 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13408;
                                    FStar_Syntax_Syntax.p = uu____13409;_},uu____13410)::[]
                                   -> body1
                               | uu____13423 ->
                                   let uu____13426 =
                                     let uu____13433 =
                                       let uu____13434 =
                                         let uu____13457 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13460 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13457, uu____13460)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13434
                                        in
                                     FStar_Syntax_Syntax.mk uu____13433  in
                                   uu____13426 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13500 =
                               let uu____13503 =
                                 let uu____13504 =
                                   let uu____13518 =
                                     let uu____13521 =
                                       let uu____13522 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13522]  in
                                     FStar_Syntax_Subst.close uu____13521
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13518)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13504  in
                               FStar_All.pipe_left mk1 uu____13503  in
                             (uu____13500, aq))
                     in
                  (match uu____13319 with | (tm,aq) -> (tm, aq))
               in
            let uu____13584 = FStar_List.hd lbs  in
            (match uu____13584 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13628 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13628
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13644 =
                let uu____13645 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13645  in
              mk1 uu____13644  in
            let uu____13646 = desugar_term_aq env t1  in
            (match uu____13646 with
             | (t1',aq1) ->
                 let uu____13657 = desugar_term_aq env t2  in
                 (match uu____13657 with
                  | (t2',aq2) ->
                      let uu____13668 = desugar_term_aq env t3  in
                      (match uu____13668 with
                       | (t3',aq3) ->
                           let uu____13679 =
                             let uu____13680 =
                               let uu____13681 =
                                 let uu____13704 =
                                   let uu____13721 =
                                     let uu____13736 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____13736,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13750 =
                                     let uu____13767 =
                                       let uu____13782 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____13782,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13767]  in
                                   uu____13721 :: uu____13750  in
                                 (t1', uu____13704)  in
                               FStar_Syntax_Syntax.Tm_match uu____13681  in
                             mk1 uu____13680  in
                           (uu____13679, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13978 =
              match uu____13978 with
              | (pat,wopt,b) ->
                  let uu____14000 = desugar_match_pat env pat  in
                  (match uu____14000 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14031 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14031
                          in
                       let uu____14036 = desugar_term_aq env1 b  in
                       (match uu____14036 with
                        | (b1,aq) ->
                            let uu____14049 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14049, aq)))
               in
            let uu____14054 = desugar_term_aq env e  in
            (match uu____14054 with
             | (e1,aq) ->
                 let uu____14065 =
                   let uu____14096 =
                     let uu____14129 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14129 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14096
                     (fun uu____14347  ->
                        match uu____14347 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14065 with
                  | (brs,aqs) ->
                      let uu____14566 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14566, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14600 =
              let uu____14621 = is_comp_type env t  in
              if uu____14621
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14676 = desugar_term_aq env t  in
                 match uu____14676 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14600 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14768 = desugar_term_aq env e  in
                 (match uu____14768 with
                  | (e1,aq) ->
                      let uu____14779 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14779, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14818,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14861 = FStar_List.hd fields  in
              match uu____14861 with | (f,uu____14873) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14919  ->
                        match uu____14919 with
                        | (g,uu____14926) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14933,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14947 =
                         let uu____14953 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14953)
                          in
                       FStar_Errors.raise_error uu____14947
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
                  let uu____14964 =
                    let uu____14975 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15006  ->
                              match uu____15006 with
                              | (f,uu____15016) ->
                                  let uu____15017 =
                                    let uu____15018 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15018
                                     in
                                  (uu____15017, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14975)  in
                  FStar_Parser_AST.Construct uu____14964
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15036 =
                      let uu____15037 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15037  in
                    FStar_Parser_AST.mk_term uu____15036
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15039 =
                      let uu____15052 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15082  ->
                                match uu____15082 with
                                | (f,uu____15092) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15052)  in
                    FStar_Parser_AST.Record uu____15039  in
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
            let uu____15152 = desugar_term_aq env recterm1  in
            (match uu____15152 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15168;
                         FStar_Syntax_Syntax.vars = uu____15169;_},args)
                      ->
                      let uu____15195 =
                        let uu____15196 =
                          let uu____15197 =
                            let uu____15214 =
                              let uu____15217 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15218 =
                                let uu____15221 =
                                  let uu____15222 =
                                    let uu____15229 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15229)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15222
                                   in
                                FStar_Pervasives_Native.Some uu____15221  in
                              FStar_Syntax_Syntax.fvar uu____15217
                                FStar_Syntax_Syntax.delta_constant
                                uu____15218
                               in
                            (uu____15214, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15197  in
                        FStar_All.pipe_left mk1 uu____15196  in
                      (uu____15195, s)
                  | uu____15258 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15262 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15262 with
              | (constrname,is_rec) ->
                  let uu____15281 = desugar_term_aq env e  in
                  (match uu____15281 with
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
                       let uu____15301 =
                         let uu____15302 =
                           let uu____15303 =
                             let uu____15320 =
                               let uu____15323 =
                                 let uu____15324 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15324
                                  in
                               FStar_Syntax_Syntax.fvar uu____15323
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____15326 =
                               let uu____15337 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15337]  in
                             (uu____15320, uu____15326)  in
                           FStar_Syntax_Syntax.Tm_app uu____15303  in
                         FStar_All.pipe_left mk1 uu____15302  in
                       (uu____15301, s))))
        | FStar_Parser_AST.NamedTyp (uu____15374,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15384 =
              let uu____15385 = FStar_Syntax_Subst.compress tm  in
              uu____15385.FStar_Syntax_Syntax.n  in
            (match uu____15384 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15393 =
                   let uu___118_15394 =
                     let uu____15395 =
                       let uu____15397 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15397  in
                     FStar_Syntax_Util.exp_string uu____15395  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___118_15394.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___118_15394.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15393, noaqs)
             | uu____15398 ->
                 let uu____15399 =
                   let uu____15405 =
                     let uu____15407 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15407
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15405)  in
                 FStar_Errors.raise_error uu____15399
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15416 = desugar_term_aq env e  in
            (match uu____15416 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15428 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15428, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15433 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15434 =
              let uu____15435 =
                let uu____15442 = desugar_term env e  in (bv, uu____15442)
                 in
              [uu____15435]  in
            (uu____15433, uu____15434)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15467 =
              let uu____15468 =
                let uu____15469 =
                  let uu____15476 = desugar_term env e  in (uu____15476, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15469  in
              FStar_All.pipe_left mk1 uu____15468  in
            (uu____15467, noaqs)
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
              let uu____15505 =
                let uu____15506 =
                  let uu____15513 =
                    let uu____15514 =
                      let uu____15515 =
                        let uu____15524 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15537 =
                          let uu____15538 =
                            let uu____15539 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15539  in
                          FStar_Parser_AST.mk_term uu____15538
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15524, uu____15537,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15515  in
                    FStar_Parser_AST.mk_term uu____15514
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15513)  in
                FStar_Parser_AST.Abs uu____15506  in
              FStar_Parser_AST.mk_term uu____15505
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
            let e1 =
              FStar_List.fold_left
                (fun e1  ->
                   fun uu____15585  ->
                     match uu____15585 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____15589 =
                           let uu____15596 =
                             let uu____15601 = eta_and_annot rel2  in
                             (uu____15601, FStar_Parser_AST.Nothing)  in
                           let uu____15602 =
                             let uu____15609 =
                               let uu____15616 =
                                 let uu____15621 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____15621, FStar_Parser_AST.Nothing)  in
                               let uu____15622 =
                                 let uu____15629 =
                                   let uu____15634 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____15634, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____15629]  in
                               uu____15616 :: uu____15622  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____15609
                              in
                           uu____15596 :: uu____15602  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____15589
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____15656 =
                let uu____15663 =
                  let uu____15668 = FStar_Parser_AST.thunk e1  in
                  (uu____15668, FStar_Parser_AST.Nothing)  in
                [uu____15663]  in
              FStar_Parser_AST.mkApp finish1 uu____15656
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____15677 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15678 = desugar_formula env top  in
            (uu____15678, noaqs)
        | uu____15679 ->
            let uu____15680 =
              let uu____15686 =
                let uu____15688 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____15688  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15686)  in
            FStar_Errors.raise_error uu____15680 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15698 -> false
    | uu____15708 -> true

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
           (fun uu____15746  ->
              match uu____15746 with
              | (a,imp) ->
                  let uu____15759 = desugar_term env a  in
                  arg_withimp_e imp uu____15759))

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
          let is_requires uu____15796 =
            match uu____15796 with
            | (t1,uu____15803) ->
                let uu____15804 =
                  let uu____15805 = unparen t1  in
                  uu____15805.FStar_Parser_AST.tm  in
                (match uu____15804 with
                 | FStar_Parser_AST.Requires uu____15807 -> true
                 | uu____15816 -> false)
             in
          let is_ensures uu____15828 =
            match uu____15828 with
            | (t1,uu____15835) ->
                let uu____15836 =
                  let uu____15837 = unparen t1  in
                  uu____15837.FStar_Parser_AST.tm  in
                (match uu____15836 with
                 | FStar_Parser_AST.Ensures uu____15839 -> true
                 | uu____15848 -> false)
             in
          let is_app head1 uu____15866 =
            match uu____15866 with
            | (t1,uu____15874) ->
                let uu____15875 =
                  let uu____15876 = unparen t1  in
                  uu____15876.FStar_Parser_AST.tm  in
                (match uu____15875 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15879;
                        FStar_Parser_AST.level = uu____15880;_},uu____15881,uu____15882)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15884 -> false)
             in
          let is_smt_pat uu____15896 =
            match uu____15896 with
            | (t1,uu____15903) ->
                let uu____15904 =
                  let uu____15905 = unparen t1  in
                  uu____15905.FStar_Parser_AST.tm  in
                (match uu____15904 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____15909);
                               FStar_Parser_AST.range = uu____15910;
                               FStar_Parser_AST.level = uu____15911;_},uu____15912)::uu____15913::[])
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
                               FStar_Parser_AST.range = uu____15962;
                               FStar_Parser_AST.level = uu____15963;_},uu____15964)::uu____15965::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____15998 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16033 = head_and_args t1  in
            match uu____16033 with
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
                     let thunk_ens uu____16126 =
                       match uu____16126 with
                       | (e,i) ->
                           let uu____16137 = FStar_Parser_AST.thunk e  in
                           (uu____16137, i)
                        in
                     let fail_lemma uu____16149 =
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
                           let uu____16255 =
                             let uu____16262 =
                               let uu____16269 = thunk_ens ens  in
                               [uu____16269; nil_pat]  in
                             req_true :: uu____16262  in
                           unit_tm :: uu____16255
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16316 =
                             let uu____16323 =
                               let uu____16330 = thunk_ens ens  in
                               [uu____16330; nil_pat]  in
                             req :: uu____16323  in
                           unit_tm :: uu____16316
                       | ens::smtpat::[] when
                           (((let uu____16379 = is_requires ens  in
                              Prims.op_Negation uu____16379) &&
                               (let uu____16382 = is_smt_pat ens  in
                                Prims.op_Negation uu____16382))
                              &&
                              (let uu____16385 = is_decreases ens  in
                               Prims.op_Negation uu____16385))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16387 =
                             let uu____16394 =
                               let uu____16401 = thunk_ens ens  in
                               [uu____16401; smtpat]  in
                             req_true :: uu____16394  in
                           unit_tm :: uu____16387
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16448 =
                             let uu____16455 =
                               let uu____16462 = thunk_ens ens  in
                               [uu____16462; nil_pat; dec]  in
                             req_true :: uu____16455  in
                           unit_tm :: uu____16448
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16522 =
                             let uu____16529 =
                               let uu____16536 = thunk_ens ens  in
                               [uu____16536; smtpat; dec]  in
                             req_true :: uu____16529  in
                           unit_tm :: uu____16522
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16596 =
                             let uu____16603 =
                               let uu____16610 = thunk_ens ens  in
                               [uu____16610; nil_pat; dec]  in
                             req :: uu____16603  in
                           unit_tm :: uu____16596
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16670 =
                             let uu____16677 =
                               let uu____16684 = thunk_ens ens  in
                               [uu____16684; smtpat]  in
                             req :: uu____16677  in
                           unit_tm :: uu____16670
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16749 =
                             let uu____16756 =
                               let uu____16763 = thunk_ens ens  in
                               [uu____16763; dec; smtpat]  in
                             req :: uu____16756  in
                           unit_tm :: uu____16749
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16825 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16825, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16853 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16853
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16856 =
                       let uu____16863 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16863, [])  in
                     (uu____16856, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16881 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16881
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16884 =
                       let uu____16891 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16891, [])  in
                     (uu____16884, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____16913 =
                       let uu____16920 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16920, [])  in
                     (uu____16913, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16943 when allow_type_promotion ->
                     let default_effect =
                       let uu____16945 = FStar_Options.ml_ish ()  in
                       if uu____16945
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____16951 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____16951
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____16958 =
                       let uu____16965 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16965, [])  in
                     (uu____16958, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16988 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17007 = pre_process_comp_typ t  in
          match uu____17007 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____17059 =
                    let uu____17065 =
                      let uu____17067 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17067
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17065)
                     in
                  fail1 uu____17059)
               else ();
               (let is_universe uu____17083 =
                  match uu____17083 with
                  | (uu____17089,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17091 = FStar_Util.take is_universe args  in
                match uu____17091 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17150  ->
                           match uu____17150 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17157 =
                      let uu____17172 = FStar_List.hd args1  in
                      let uu____17181 = FStar_List.tl args1  in
                      (uu____17172, uu____17181)  in
                    (match uu____17157 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17236 =
                           let is_decrease uu____17275 =
                             match uu____17275 with
                             | (t1,uu____17286) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17297;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17298;_},uu____17299::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17338 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17236 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17455  ->
                                        match uu____17455 with
                                        | (t1,uu____17465) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17474,(arg,uu____17476)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17515 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17536 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17548 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17548
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17555 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17555
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags1 =
                                      let uu____17565 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17565
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17572 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17572
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17579 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17579
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17586 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17586
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags2 =
                                      FStar_List.append flags1 cattributes
                                       in
                                    let rest3 =
                                      let uu____17607 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17607
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
                                                    let uu____17698 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17698
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
                                              | uu____17719 -> pat  in
                                            let uu____17720 =
                                              let uu____17731 =
                                                let uu____17742 =
                                                  let uu____17751 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17751, aq)  in
                                                [uu____17742]  in
                                              ens :: uu____17731  in
                                            req :: uu____17720
                                        | uu____17792 -> rest2
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
        | uu____17824 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___119_17846 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___119_17846.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___119_17846.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___120_17888 = b  in
             {
               FStar_Parser_AST.b = (uu___120_17888.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___120_17888.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___120_17888.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____17951 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____17951)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____17964 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____17964 with
             | (env1,a1) ->
                 let a2 =
                   let uu___121_17974 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___121_17974.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___121_17974.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____18000 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____18014 =
                     let uu____18017 =
                       let uu____18018 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18018]  in
                     no_annot_abs uu____18017 body2  in
                   FStar_All.pipe_left setpos uu____18014  in
                 let uu____18039 =
                   let uu____18040 =
                     let uu____18057 =
                       let uu____18060 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18060
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____18062 =
                       let uu____18073 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18073]  in
                     (uu____18057, uu____18062)  in
                   FStar_Syntax_Syntax.Tm_app uu____18040  in
                 FStar_All.pipe_left mk1 uu____18039)
        | uu____18112 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18193 = q (rest, pats, body)  in
              let uu____18200 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18193 uu____18200
                FStar_Parser_AST.Formula
               in
            let uu____18201 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____18201 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18210 -> failwith "impossible"  in
      let uu____18214 =
        let uu____18215 = unparen f  in uu____18215.FStar_Parser_AST.tm  in
      match uu____18214 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18228,uu____18229) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18241,uu____18242) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18274 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____18274
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18310 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____18310
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18354 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18359 =
        FStar_List.fold_left
          (fun uu____18392  ->
             fun b  ->
               match uu____18392 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___122_18436 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___122_18436.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___122_18436.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___122_18436.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18451 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18451 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___123_18469 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___123_18469.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___123_18469.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18470 =
                               let uu____18477 =
                                 let uu____18482 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18482)  in
                               uu____18477 :: out  in
                             (env2, uu____18470))
                    | uu____18493 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18359 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____18566 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18566)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18571 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18571)
      | FStar_Parser_AST.TVariable x ->
          let uu____18575 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18575)
      | FStar_Parser_AST.NoName t ->
          let uu____18579 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18579)
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
      fun uu___73_18587  ->
        match uu___73_18587 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18609 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18609, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18626 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18626 with
             | (env1,a1) ->
                 let uu____18643 =
                   let uu____18650 = trans_aqual env1 imp  in
                   ((let uu___124_18656 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___124_18656.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___124_18656.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18650)
                    in
                 (uu____18643, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___74_18664  ->
      match uu___74_18664 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18668 =
            let uu____18669 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18669  in
          FStar_Pervasives_Native.Some uu____18668
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____18685) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____18687) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18690 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____18708 = binder_ident b  in
         FStar_Common.list_of_option uu____18708) bs
  
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
               (fun uu___75_18745  ->
                  match uu___75_18745 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____18750 -> false))
           in
        let quals2 q =
          let uu____18764 =
            (let uu____18768 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____18768) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____18764
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____18785 = FStar_Ident.range_of_lid disc_name  in
                let uu____18786 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____18785;
                  FStar_Syntax_Syntax.sigquals = uu____18786;
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
            let uu____18826 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____18864  ->
                        match uu____18864 with
                        | (x,uu____18875) ->
                            let uu____18880 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____18880 with
                             | (field_name,uu____18888) ->
                                 let only_decl =
                                   ((let uu____18893 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____18893)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____18895 =
                                        let uu____18897 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____18897.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____18895)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____18915 =
                                       FStar_List.filter
                                         (fun uu___76_18919  ->
                                            match uu___76_18919 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____18922 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____18915
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___77_18937  ->
                                             match uu___77_18937 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____18942 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____18945 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____18945;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____18952 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____18952
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____18963 =
                                        let uu____18968 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____18968  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____18963;
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
                                      let uu____18972 =
                                        let uu____18973 =
                                          let uu____18980 =
                                            let uu____18983 =
                                              let uu____18984 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____18984
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____18983]  in
                                          ((false, [lb]), uu____18980)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____18973
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____18972;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____18826 FStar_List.flatten
  
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
            (lid,uu____19033,t,uu____19035,n1,uu____19037) when
            let uu____19044 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____19044 ->
            let uu____19046 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____19046 with
             | (formals,uu____19064) ->
                 (match formals with
                  | [] -> []
                  | uu____19093 ->
                      let filter_records uu___78_19109 =
                        match uu___78_19109 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19112,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19124 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19126 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19126 with
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
                      let uu____19138 = FStar_Util.first_N n1 formals  in
                      (match uu____19138 with
                       | (uu____19167,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19201 -> []
  
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
                    let uu____19280 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19280
                    then
                      let uu____19286 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19286
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19290 =
                      let uu____19295 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19295  in
                    let uu____19296 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19302 =
                          let uu____19305 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19305  in
                        FStar_Syntax_Util.arrow typars uu____19302
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19310 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19290;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19296;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19310;
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
          let tycon_id uu___79_19364 =
            match uu___79_19364 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19366,uu____19367) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19377,uu____19378,uu____19379) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19389,uu____19390,uu____19391) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19421,uu____19422,uu____19423) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19469) ->
                let uu____19470 =
                  let uu____19471 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19471  in
                FStar_Parser_AST.mk_term uu____19470 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19473 =
                  let uu____19474 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19474  in
                FStar_Parser_AST.mk_term uu____19473 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19476) ->
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
              | uu____19507 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19515 =
                     let uu____19516 =
                       let uu____19523 = binder_to_term b  in
                       (out, uu____19523, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19516  in
                   FStar_Parser_AST.mk_term uu____19515
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___80_19535 =
            match uu___80_19535 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19592  ->
                       match uu____19592 with
                       | (x,t,uu____19603) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19609 =
                    let uu____19610 =
                      let uu____19611 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19611  in
                    FStar_Parser_AST.mk_term uu____19610
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19609 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19618 = binder_idents parms  in id1 ::
                    uu____19618
                   in
                (FStar_List.iter
                   (fun uu____19636  ->
                      match uu____19636 with
                      | (f,uu____19646,uu____19647) ->
                          let uu____19652 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19652
                          then
                            let uu____19657 =
                              let uu____19663 =
                                let uu____19665 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19665
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19663)
                               in
                            FStar_Errors.raise_error uu____19657
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19671 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____19698  ->
                            match uu____19698 with
                            | (x,uu____19708,uu____19709) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19671)))
            | uu____19767 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___81_19807 =
            match uu___81_19807 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____19831 = typars_of_binders _env binders  in
                (match uu____19831 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____19867 =
                         let uu____19868 =
                           let uu____19869 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____19869  in
                         FStar_Parser_AST.mk_term uu____19868
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____19867 binders  in
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
            | uu____19880 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____19923 =
              FStar_List.fold_left
                (fun uu____19957  ->
                   fun uu____19958  ->
                     match (uu____19957, uu____19958) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20027 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20027 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____19923 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20118 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20118
                | uu____20119 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20127 = desugar_abstract_tc quals env [] tc  in
              (match uu____20127 with
               | (uu____20140,uu____20141,se,uu____20143) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20146,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20165 =
                                 let uu____20167 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20167  in
                               if uu____20165
                               then
                                 let uu____20170 =
                                   let uu____20176 =
                                     let uu____20178 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20178
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20176)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20170
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
                           | uu____20191 ->
                               let uu____20192 =
                                 let uu____20199 =
                                   let uu____20200 =
                                     let uu____20215 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20215)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20200
                                    in
                                 FStar_Syntax_Syntax.mk uu____20199  in
                               uu____20192 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___125_20231 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___125_20231.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___125_20231.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___125_20231.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20232 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20236 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20236
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20249 = typars_of_binders env binders  in
              (match uu____20249 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20283 =
                           FStar_Util.for_some
                             (fun uu___82_20286  ->
                                match uu___82_20286 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20289 -> false) quals
                            in
                         if uu____20283
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20297 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20297
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20302 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___83_20308  ->
                               match uu___83_20308 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20311 -> false))
                        in
                     if uu____20302
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20325 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20325
                     then
                       let uu____20331 =
                         let uu____20338 =
                           let uu____20339 = unparen t  in
                           uu____20339.FStar_Parser_AST.tm  in
                         match uu____20338 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20360 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20390)::args_rev ->
                                   let uu____20402 =
                                     let uu____20403 = unparen last_arg  in
                                     uu____20403.FStar_Parser_AST.tm  in
                                   (match uu____20402 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20431 -> ([], args))
                               | uu____20440 -> ([], args)  in
                             (match uu____20360 with
                              | (cattributes,args1) ->
                                  let uu____20479 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20479))
                         | uu____20490 -> (t, [])  in
                       match uu____20331 with
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
                                  (fun uu___84_20513  ->
                                     match uu___84_20513 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20516 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____20525)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20549 = tycon_record_as_variant trec  in
              (match uu____20549 with
               | (t,fs) ->
                   let uu____20566 =
                     let uu____20569 =
                       let uu____20570 =
                         let uu____20579 =
                           let uu____20582 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20582  in
                         (uu____20579, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20570  in
                     uu____20569 :: quals  in
                   desugar_tycon env d uu____20566 [t])
          | uu____20587::uu____20588 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____20758 = et  in
                match uu____20758 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____20988 ->
                         let trec = tc  in
                         let uu____21012 = tycon_record_as_variant trec  in
                         (match uu____21012 with
                          | (t,fs) ->
                              let uu____21072 =
                                let uu____21075 =
                                  let uu____21076 =
                                    let uu____21085 =
                                      let uu____21088 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21088  in
                                    (uu____21085, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21076
                                   in
                                uu____21075 :: quals1  in
                              collect_tcs uu____21072 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21178 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21178 with
                          | (env2,uu____21239,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21392 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21392 with
                          | (env2,uu____21453,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21581 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21631 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21631 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___86_22146  ->
                             match uu___86_22146 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22212,uu____22213);
                                    FStar_Syntax_Syntax.sigrng = uu____22214;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22215;
                                    FStar_Syntax_Syntax.sigmeta = uu____22216;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22217;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22281 =
                                     typars_of_binders env1 binders  in
                                   match uu____22281 with
                                   | (env2,tpars1) ->
                                       let uu____22308 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22308 with
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
                                 let uu____22337 =
                                   let uu____22356 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22356)
                                    in
                                 [uu____22337]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22416);
                                    FStar_Syntax_Syntax.sigrng = uu____22417;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22419;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22420;_},constrs,tconstr,quals1)
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
                                 let uu____22521 = push_tparams env1 tpars
                                    in
                                 (match uu____22521 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22588  ->
                                             match uu____22588 with
                                             | (x,uu____22600) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22605 =
                                        let uu____22632 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____22742  ->
                                                  match uu____22742 with
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
                                                        let uu____22802 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____22802
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
                                                                uu___85_22813
                                                                 ->
                                                                match uu___85_22813
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____22825
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____22833 =
                                                        let uu____22852 =
                                                          let uu____22853 =
                                                            let uu____22854 =
                                                              let uu____22870
                                                                =
                                                                let uu____22871
                                                                  =
                                                                  let uu____22874
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____22874
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____22871
                                                                 in
                                                              (name, univs1,
                                                                uu____22870,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____22854
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____22853;
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
                                                          uu____22852)
                                                         in
                                                      (name, uu____22833)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22632
                                         in
                                      (match uu____22605 with
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
                             | uu____23090 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23218  ->
                             match uu____23218 with
                             | (name_doc,uu____23244,uu____23245) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23317  ->
                             match uu____23317 with
                             | (uu____23336,uu____23337,se) -> se))
                      in
                   let uu____23363 =
                     let uu____23370 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23370 rng
                      in
                   (match uu____23363 with
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
                               (fun uu____23432  ->
                                  match uu____23432 with
                                  | (uu____23453,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23501,tps,k,uu____23504,constrs)
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
                                      let uu____23525 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23540 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23557,uu____23558,uu____23559,uu____23560,uu____23561)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23568
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23540
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23572 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___87_23579  ->
                                                          match uu___87_23579
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23581 ->
                                                              true
                                                          | uu____23591 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23572))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23525
                                  | uu____23593 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23610  ->
                                 match uu____23610 with
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
      let uu____23655 =
        FStar_List.fold_left
          (fun uu____23690  ->
             fun b  ->
               match uu____23690 with
               | (env1,binders1) ->
                   let uu____23734 = desugar_binder env1 b  in
                   (match uu____23734 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____23757 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____23757 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____23810 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23655 with
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
          let uu____23914 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___88_23921  ->
                    match uu___88_23921 with
                    | FStar_Syntax_Syntax.Reflectable uu____23923 -> true
                    | uu____23925 -> false))
             in
          if uu____23914
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____23930 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____23930
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
      let uu____23971 = FStar_Syntax_Util.head_and_args at1  in
      match uu____23971 with
      | (hd1,args) ->
          let uu____24024 =
            let uu____24039 =
              let uu____24040 = FStar_Syntax_Subst.compress hd1  in
              uu____24040.FStar_Syntax_Syntax.n  in
            (uu____24039, args)  in
          (match uu____24024 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____24065)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____24100 =
                 let uu____24105 =
                   let uu____24114 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____24114 a1  in
                 uu____24105 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____24100 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____24144 =
                      let uu____24153 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____24153, b)  in
                    FStar_Pervasives_Native.Some uu____24144
                | uu____24170 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____24224) when
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
           | uu____24259 -> FStar_Pervasives_Native.None)
  
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
                  let uu____24431 = desugar_binders monad_env eff_binders  in
                  match uu____24431 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____24471 =
                          let uu____24473 =
                            let uu____24482 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24482  in
                          FStar_List.length uu____24473  in
                        uu____24471 = (Prims.parse_int "1")  in
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
                            (uu____24566,uu____24567,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24569,uu____24570,uu____24571),uu____24572)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24609 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24612 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24624 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24624 mandatory_members)
                          eff_decls
                         in
                      (match uu____24612 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24643 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____24672  ->
                                     fun decl  ->
                                       match uu____24672 with
                                       | (env2,out) ->
                                           let uu____24692 =
                                             desugar_decl env2 decl  in
                                           (match uu____24692 with
                                            | (env3,ses) ->
                                                let uu____24705 =
                                                  let uu____24708 =
                                                    FStar_List.hd ses  in
                                                  uu____24708 :: out  in
                                                (env3, uu____24705)))
                                  (env1, []))
                              in
                           (match uu____24643 with
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
                                              (uu____24777,uu____24778,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24781,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____24782,(def,uu____24784)::
                                                      (cps_type,uu____24786)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____24787;
                                                   FStar_Parser_AST.level =
                                                     uu____24788;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____24844 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24844 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24882 =
                                                     let uu____24883 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24884 =
                                                       let uu____24885 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24885
                                                        in
                                                     let uu____24892 =
                                                       let uu____24893 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24893
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24883;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24884;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____24892
                                                     }  in
                                                   (uu____24882, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____24902,uu____24903,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24906,defn),doc1)::[])
                                              when for_free ->
                                              let uu____24945 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24945 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24983 =
                                                     let uu____24984 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24985 =
                                                       let uu____24986 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24986
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24984;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24985;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____24983, doc1))
                                          | uu____24995 ->
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
                                    let uu____25031 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____25031
                                     in
                                  let uu____25033 =
                                    let uu____25034 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____25034
                                     in
                                  ([], uu____25033)  in
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
                                      let uu____25052 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____25052)  in
                                    let uu____25059 =
                                      let uu____25060 =
                                        let uu____25061 =
                                          let uu____25062 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25062
                                           in
                                        let uu____25072 = lookup1 "return"
                                           in
                                        let uu____25074 = lookup1 "bind"  in
                                        let uu____25076 =
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
                                            uu____25061;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____25072;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____25074;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____25076
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____25060
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____25059;
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
                                         (fun uu___89_25084  ->
                                            match uu___89_25084 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____25087 -> true
                                            | uu____25089 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____25104 =
                                       let uu____25105 =
                                         let uu____25106 =
                                           lookup1 "return_wp"  in
                                         let uu____25108 = lookup1 "bind_wp"
                                            in
                                         let uu____25110 =
                                           lookup1 "if_then_else"  in
                                         let uu____25112 = lookup1 "ite_wp"
                                            in
                                         let uu____25114 = lookup1 "stronger"
                                            in
                                         let uu____25116 = lookup1 "close_wp"
                                            in
                                         let uu____25118 = lookup1 "assert_p"
                                            in
                                         let uu____25120 = lookup1 "assume_p"
                                            in
                                         let uu____25122 = lookup1 "null_wp"
                                            in
                                         let uu____25124 = lookup1 "trivial"
                                            in
                                         let uu____25126 =
                                           if rr
                                           then
                                             let uu____25128 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____25128
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____25146 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____25151 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____25156 =
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
                                             uu____25106;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____25108;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____25110;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____25112;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____25114;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____25116;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____25118;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____25120;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____25122;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____25124;
                                           FStar_Syntax_Syntax.repr =
                                             uu____25126;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25146;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25151;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____25156
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____25105
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____25104;
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
                                          fun uu____25182  ->
                                            match uu____25182 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____25196 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____25196
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
                let uu____25220 = desugar_binders env1 eff_binders  in
                match uu____25220 with
                | (env2,binders) ->
                    let uu____25257 =
                      let uu____25268 = head_and_args defn  in
                      match uu____25268 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25305 ->
                                let uu____25306 =
                                  let uu____25312 =
                                    let uu____25314 =
                                      let uu____25316 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25316 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25314  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25312)
                                   in
                                FStar_Errors.raise_error uu____25306
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25322 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25352)::args_rev ->
                                let uu____25364 =
                                  let uu____25365 = unparen last_arg  in
                                  uu____25365.FStar_Parser_AST.tm  in
                                (match uu____25364 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25393 -> ([], args))
                            | uu____25402 -> ([], args)  in
                          (match uu____25322 with
                           | (cattributes,args1) ->
                               let uu____25445 = desugar_args env2 args1  in
                               let uu____25446 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25445, uu____25446))
                       in
                    (match uu____25257 with
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
                          (let uu____25486 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25486 with
                           | (ed_binders,uu____25500,ed_binders_opening) ->
                               let sub' shift_n uu____25519 =
                                 match uu____25519 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25534 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25534 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25538 =
                                       let uu____25539 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25539)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25538
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25560 =
                                   let uu____25561 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25561
                                    in
                                 let uu____25576 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____25577 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____25578 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25579 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25580 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25581 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25582 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____25583 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____25584 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____25585 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25586 =
                                   let uu____25587 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____25587
                                    in
                                 let uu____25602 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____25603 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____25604 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____25620 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25621 =
                                          let uu____25622 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25622
                                           in
                                        let uu____25643 =
                                          let uu____25644 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25644
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25620;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25621;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25643
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
                                     uu____25560;
                                   FStar_Syntax_Syntax.ret_wp = uu____25576;
                                   FStar_Syntax_Syntax.bind_wp = uu____25577;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25578;
                                   FStar_Syntax_Syntax.ite_wp = uu____25579;
                                   FStar_Syntax_Syntax.stronger = uu____25580;
                                   FStar_Syntax_Syntax.close_wp = uu____25581;
                                   FStar_Syntax_Syntax.assert_p = uu____25582;
                                   FStar_Syntax_Syntax.assume_p = uu____25583;
                                   FStar_Syntax_Syntax.null_wp = uu____25584;
                                   FStar_Syntax_Syntax.trivial = uu____25585;
                                   FStar_Syntax_Syntax.repr = uu____25586;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____25602;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____25603;
                                   FStar_Syntax_Syntax.actions = uu____25604;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____25668 =
                                     let uu____25670 =
                                       let uu____25679 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____25679
                                        in
                                     FStar_List.length uu____25670  in
                                   uu____25668 = (Prims.parse_int "1")  in
                                 let uu____25712 =
                                   let uu____25715 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____25715 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____25712;
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
                                             let uu____25739 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____25739
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____25741 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____25741
                                 then
                                   let reflect_lid =
                                     let uu____25748 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____25748
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
    let uu____25760 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____25760 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____25845 ->
              let uu____25848 =
                let uu____25850 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____25850
                 in
              Prims.op_Hat "\n  " uu____25848
          | uu____25853 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____25872  ->
               match uu____25872 with
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
          let uu____25917 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____25917
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____25920 =
          let uu____25931 = FStar_Syntax_Syntax.as_arg arg  in [uu____25931]
           in
        FStar_Syntax_Util.mk_app fv uu____25920

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____25962 = desugar_decl_noattrs env d  in
      match uu____25962 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____25980 = mk_comment_attr d  in uu____25980 :: attrs1  in
          let uu____25981 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___126_25991 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___126_25991.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___126_25991.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___126_25991.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___126_25991.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___127_25994 = sigelt  in
                      let uu____25995 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____26001 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____26001) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___127_25994.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___127_25994.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___127_25994.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___127_25994.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____25995
                      })) sigelts
             in
          (env1, uu____25981)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26027 = desugar_decl_aux env d  in
      match uu____26027 with
      | (env1,ses) ->
          let uu____26038 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26038)

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
      | FStar_Parser_AST.Fsdoc uu____26066 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____26071 = FStar_Syntax_DsEnv.iface env  in
          if uu____26071
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26086 =
               let uu____26088 =
                 let uu____26090 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26091 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26090
                   uu____26091
                  in
               Prims.op_Negation uu____26088  in
             if uu____26086
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26105 =
                  let uu____26107 =
                    let uu____26109 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26109 lid  in
                  Prims.op_Negation uu____26107  in
                if uu____26105
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26123 =
                     let uu____26125 =
                       let uu____26127 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26127
                         lid
                        in
                     Prims.op_Negation uu____26125  in
                   if uu____26123
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26145 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26145, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26186,uu____26187)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26226 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26253  ->
                 match uu____26253 with | (x,uu____26261) -> x) tcs
             in
          let uu____26266 =
            let uu____26271 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26271 tcs1  in
          (match uu____26266 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26288 =
                   let uu____26289 =
                     let uu____26296 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26296  in
                   [uu____26289]  in
                 let uu____26309 =
                   let uu____26312 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26315 =
                     let uu____26326 =
                       let uu____26335 =
                         let uu____26336 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26336  in
                       FStar_Syntax_Syntax.as_arg uu____26335  in
                     [uu____26326]  in
                   FStar_Syntax_Util.mk_app uu____26312 uu____26315  in
                 FStar_Syntax_Util.abs uu____26288 uu____26309
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26376,id1))::uu____26378 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26381::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26385 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26385 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26391 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26391]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26412) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26422,uu____26423,uu____26424,uu____26425,uu____26426)
                     ->
                     let uu____26435 =
                       let uu____26436 =
                         let uu____26437 =
                           let uu____26444 = mkclass lid  in
                           (meths, uu____26444)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26437  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26436;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26435]
                 | uu____26447 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26481;
                    FStar_Parser_AST.prange = uu____26482;_},uu____26483)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26493;
                    FStar_Parser_AST.prange = uu____26494;_},uu____26495)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26511;
                         FStar_Parser_AST.prange = uu____26512;_},uu____26513);
                    FStar_Parser_AST.prange = uu____26514;_},uu____26515)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26537;
                         FStar_Parser_AST.prange = uu____26538;_},uu____26539);
                    FStar_Parser_AST.prange = uu____26540;_},uu____26541)::[]
                   -> false
               | (p,uu____26570)::[] ->
                   let uu____26579 = is_app_pattern p  in
                   Prims.op_Negation uu____26579
               | uu____26581 -> false)
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
            let uu____26656 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26656 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26669 =
                     let uu____26670 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26670.FStar_Syntax_Syntax.n  in
                   match uu____26669 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26680) ->
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
                         | uu____26716::uu____26717 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____26720 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___90_26736  ->
                                     match uu___90_26736 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____26739;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26740;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26741;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26742;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26743;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26744;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26745;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26757;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26758;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26759;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26760;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26761;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26762;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____26776 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____26809  ->
                                   match uu____26809 with
                                   | (uu____26823,(uu____26824,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____26776
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____26844 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____26844
                         then
                           let uu____26850 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___128_26865 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___129_26867 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___129_26867.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___129_26867.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___128_26865.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___128_26865.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___128_26865.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___128_26865.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___128_26865.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___128_26865.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____26850)
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
                   | uu____26897 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____26905 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____26924 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____26905 with
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
                       let uu___130_26961 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___130_26961.FStar_Parser_AST.prange)
                       }
                   | uu____26968 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___131_26975 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___131_26975.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___131_26975.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___131_26975.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____27011 id1 =
                   match uu____27011 with
                   | (env1,ses) ->
                       let main =
                         let uu____27032 =
                           let uu____27033 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____27033  in
                         FStar_Parser_AST.mk_term uu____27032
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
                       let uu____27083 = desugar_decl env1 id_decl  in
                       (match uu____27083 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____27101 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____27101 FStar_Util.set_elements
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
            let uu____27125 = close_fun env t  in
            desugar_term env uu____27125  in
          let quals1 =
            let uu____27129 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27129
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27141 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27141;
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
                let uu____27155 =
                  let uu____27164 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27164]  in
                let uu____27183 =
                  let uu____27186 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27186
                   in
                FStar_Syntax_Util.arrow uu____27155 uu____27183
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
            let uu____27241 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27241 with
            | FStar_Pervasives_Native.None  ->
                let uu____27244 =
                  let uu____27250 =
                    let uu____27252 =
                      let uu____27254 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____27254 " not found"  in
                    Prims.op_Hat "Effect name " uu____27252  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27250)  in
                FStar_Errors.raise_error uu____27244
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27262 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27280 =
                  let uu____27283 =
                    let uu____27284 = desugar_term env t  in
                    ([], uu____27284)  in
                  FStar_Pervasives_Native.Some uu____27283  in
                (uu____27280, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27297 =
                  let uu____27300 =
                    let uu____27301 = desugar_term env wp  in
                    ([], uu____27301)  in
                  FStar_Pervasives_Native.Some uu____27300  in
                let uu____27308 =
                  let uu____27311 =
                    let uu____27312 = desugar_term env t  in
                    ([], uu____27312)  in
                  FStar_Pervasives_Native.Some uu____27311  in
                (uu____27297, uu____27308)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27324 =
                  let uu____27327 =
                    let uu____27328 = desugar_term env t  in
                    ([], uu____27328)  in
                  FStar_Pervasives_Native.Some uu____27327  in
                (FStar_Pervasives_Native.None, uu____27324)
             in
          (match uu____27262 with
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
            let uu____27362 =
              let uu____27363 =
                let uu____27370 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27370, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27363  in
            {
              FStar_Syntax_Syntax.sigel = uu____27362;
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
      let uu____27397 =
        FStar_List.fold_left
          (fun uu____27417  ->
             fun d  ->
               match uu____27417 with
               | (env1,sigelts) ->
                   let uu____27437 = desugar_decl env1 d  in
                   (match uu____27437 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27397 with
      | (env1,sigelts) ->
          let rec forward acc uu___92_27482 =
            match uu___92_27482 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____27496,FStar_Syntax_Syntax.Sig_let uu____27497) ->
                     let uu____27510 =
                       let uu____27513 =
                         let uu___132_27514 = se2  in
                         let uu____27515 =
                           let uu____27518 =
                             FStar_List.filter
                               (fun uu___91_27532  ->
                                  match uu___91_27532 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____27537;
                                           FStar_Syntax_Syntax.vars =
                                             uu____27538;_},uu____27539);
                                      FStar_Syntax_Syntax.pos = uu____27540;
                                      FStar_Syntax_Syntax.vars = uu____27541;_}
                                      when
                                      let uu____27568 =
                                        let uu____27570 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____27570
                                         in
                                      uu____27568 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____27574 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____27518
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___132_27514.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___132_27514.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___132_27514.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___132_27514.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____27515
                         }  in
                       uu____27513 :: se1 :: acc  in
                     forward uu____27510 sigelts1
                 | uu____27580 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____27588 = forward [] sigelts  in (env1, uu____27588)
  
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
          | (FStar_Pervasives_Native.None ,uu____27653) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27657;
               FStar_Syntax_Syntax.exports = uu____27658;
               FStar_Syntax_Syntax.is_interface = uu____27659;_},FStar_Parser_AST.Module
             (current_lid,uu____27661)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27670) ->
              let uu____27673 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27673
           in
        let uu____27678 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____27720 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27720, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____27742 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27742, mname, decls, false)
           in
        match uu____27678 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____27784 = desugar_decls env2 decls  in
            (match uu____27784 with
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
          let uu____27852 =
            (FStar_Options.interactive ()) &&
              (let uu____27855 =
                 let uu____27857 =
                   let uu____27859 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____27859  in
                 FStar_Util.get_file_extension uu____27857  in
               FStar_List.mem uu____27855 ["fsti"; "fsi"])
             in
          if uu____27852 then as_interface m else m  in
        let uu____27873 = desugar_modul_common curmod env m1  in
        match uu____27873 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____27895 = FStar_Syntax_DsEnv.pop ()  in
              (uu____27895, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____27917 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____27917 with
      | (env1,modul,pop_when_done) ->
          let uu____27934 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____27934 with
           | (env2,modul1) ->
               ((let uu____27946 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____27946
                 then
                   let uu____27949 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____27949
                 else ());
                (let uu____27954 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____27954, modul1))))
  
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
        (fun uu____28008  ->
           let uu____28009 = desugar_modul env modul  in
           match uu____28009 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28051  ->
           let uu____28052 = desugar_decls env decls  in
           match uu____28052 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28107  ->
             let uu____28108 = desugar_partial_modul modul env a_modul  in
             match uu____28108 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28207 ->
                  let t =
                    let uu____28217 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28217  in
                  let uu____28230 =
                    let uu____28231 = FStar_Syntax_Subst.compress t  in
                    uu____28231.FStar_Syntax_Syntax.n  in
                  (match uu____28230 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28243,uu____28244)
                       -> bs1
                   | uu____28269 -> failwith "Impossible")
               in
            let uu____28279 =
              let uu____28286 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28286
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28279 with
            | (binders,uu____28288,binders_opening) ->
                let erase_term t =
                  let uu____28296 =
                    let uu____28297 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28297  in
                  FStar_Syntax_Subst.close binders uu____28296  in
                let erase_tscheme uu____28315 =
                  match uu____28315 with
                  | (us,t) ->
                      let t1 =
                        let uu____28335 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28335 t  in
                      let uu____28338 =
                        let uu____28339 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28339  in
                      ([], uu____28338)
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
                    | uu____28362 ->
                        let bs =
                          let uu____28372 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28372  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28412 =
                          let uu____28413 =
                            let uu____28416 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28416  in
                          uu____28413.FStar_Syntax_Syntax.n  in
                        (match uu____28412 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28418,uu____28419) -> bs1
                         | uu____28444 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28452 =
                      let uu____28453 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28453  in
                    FStar_Syntax_Subst.close binders uu____28452  in
                  let uu___133_28454 = action  in
                  let uu____28455 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28456 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___133_28454.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___133_28454.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28455;
                    FStar_Syntax_Syntax.action_typ = uu____28456
                  }  in
                let uu___134_28457 = ed  in
                let uu____28458 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28459 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____28460 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____28461 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____28462 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28463 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28464 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28465 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28466 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____28467 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____28468 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____28469 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28470 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____28471 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____28472 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____28473 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___134_28457.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___134_28457.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28458;
                  FStar_Syntax_Syntax.signature = uu____28459;
                  FStar_Syntax_Syntax.ret_wp = uu____28460;
                  FStar_Syntax_Syntax.bind_wp = uu____28461;
                  FStar_Syntax_Syntax.if_then_else = uu____28462;
                  FStar_Syntax_Syntax.ite_wp = uu____28463;
                  FStar_Syntax_Syntax.stronger = uu____28464;
                  FStar_Syntax_Syntax.close_wp = uu____28465;
                  FStar_Syntax_Syntax.assert_p = uu____28466;
                  FStar_Syntax_Syntax.assume_p = uu____28467;
                  FStar_Syntax_Syntax.null_wp = uu____28468;
                  FStar_Syntax_Syntax.trivial = uu____28469;
                  FStar_Syntax_Syntax.repr = uu____28470;
                  FStar_Syntax_Syntax.return_repr = uu____28471;
                  FStar_Syntax_Syntax.bind_repr = uu____28472;
                  FStar_Syntax_Syntax.actions = uu____28473;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___134_28457.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___135_28489 = se  in
                  let uu____28490 =
                    let uu____28491 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28491  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28490;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___135_28489.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___135_28489.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___135_28489.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___135_28489.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___136_28495 = se  in
                  let uu____28496 =
                    let uu____28497 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28497
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28496;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___136_28495.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___136_28495.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___136_28495.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___136_28495.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28499 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28500 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28500 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28517 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28517
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28519 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28519)
  