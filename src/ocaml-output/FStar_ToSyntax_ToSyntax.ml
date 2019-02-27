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
             (fun uu____57501  ->
                match uu____57501 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____57556  ->
                             match uu____57556 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____57574 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____57574 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____57580 =
                                     let uu____57581 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____57581]  in
                                   FStar_Syntax_Subst.close uu____57580
                                     branch1
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
      fun uu___429_57638  ->
        match uu___429_57638 with
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
  fun uu___430_57658  ->
    match uu___430_57658 with
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
  fun uu___431_57676  ->
    match uu___431_57676 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____57679 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____57687 .
    FStar_Parser_AST.imp ->
      'Auu____57687 ->
        ('Auu____57687 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____57713 .
    FStar_Parser_AST.imp ->
      'Auu____57713 ->
        ('Auu____57713 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____57732 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____57753 -> true
            | uu____57759 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____57768 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57775 =
      let uu____57776 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____57776  in
    FStar_Parser_AST.mk_term uu____57775 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57786 =
      let uu____57787 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____57787  in
    FStar_Parser_AST.mk_term uu____57786 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____57803 =
        let uu____57804 = unparen t  in uu____57804.FStar_Parser_AST.tm  in
      match uu____57803 with
      | FStar_Parser_AST.Name l ->
          let uu____57807 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57807 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____57814) ->
          let uu____57827 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57827 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____57834,uu____57835) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____57840,uu____57841) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____57846,t1) -> is_comp_type env t1
      | uu____57848 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____57949;
                            FStar_Syntax_Syntax.vars = uu____57950;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____57978 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____57978 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____57994 =
                               let uu____57995 =
                                 let uu____57998 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____57998  in
                               uu____57995.FStar_Syntax_Syntax.n  in
                             match uu____57994 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____58021))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____58028 -> msg
                           else msg  in
                         let uu____58031 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58031
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____58036 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____58036 " is deprecated"  in
                         let uu____58039 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58039
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____58041 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____58057 .
    'Auu____58057 ->
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
        let uu____58110 =
          let uu____58113 =
            let uu____58114 =
              let uu____58120 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____58120, r)  in
            FStar_Ident.mk_ident uu____58114  in
          [uu____58113]  in
        FStar_All.pipe_right uu____58110 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____58136 .
    env_t ->
      Prims.int ->
        'Auu____58136 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____58174 =
              let uu____58175 =
                let uu____58176 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____58176 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____58175 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____58174  in
          let fallback uu____58184 =
            let uu____58185 = FStar_Ident.text_of_id op  in
            match uu____58185 with
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
                let uu____58206 = FStar_Options.ml_ish ()  in
                if uu____58206
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
            | uu____58231 -> FStar_Pervasives_Native.None  in
          let uu____58233 =
            let uu____58236 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_58242 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_58242.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_58242.FStar_Syntax_Syntax.vars)
                 }) env true uu____58236
             in
          match uu____58233 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____58247 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____58262 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____58262
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____58311 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____58315 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____58315 with | (env1,uu____58327) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____58330,term) ->
          let uu____58332 = free_type_vars env term  in (env, uu____58332)
      | FStar_Parser_AST.TAnnotated (id1,uu____58338) ->
          let uu____58339 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____58339 with | (env1,uu____58351) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____58355 = free_type_vars env t  in (env, uu____58355)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____58362 =
        let uu____58363 = unparen t  in uu____58363.FStar_Parser_AST.tm  in
      match uu____58362 with
      | FStar_Parser_AST.Labeled uu____58366 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____58379 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____58379 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____58384 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____58387 -> []
      | FStar_Parser_AST.Uvar uu____58388 -> []
      | FStar_Parser_AST.Var uu____58389 -> []
      | FStar_Parser_AST.Projector uu____58390 -> []
      | FStar_Parser_AST.Discrim uu____58395 -> []
      | FStar_Parser_AST.Name uu____58396 -> []
      | FStar_Parser_AST.Requires (t1,uu____58398) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____58406) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____58413,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____58432,ts) ->
          FStar_List.collect
            (fun uu____58453  ->
               match uu____58453 with
               | (t1,uu____58461) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____58462,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____58470) ->
          let uu____58471 = free_type_vars env t1  in
          let uu____58474 = free_type_vars env t2  in
          FStar_List.append uu____58471 uu____58474
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____58479 = free_type_vars_b env b  in
          (match uu____58479 with
           | (env1,f) ->
               let uu____58494 = free_type_vars env1 t1  in
               FStar_List.append f uu____58494)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____58511 =
            FStar_List.fold_left
              (fun uu____58535  ->
                 fun bt  ->
                   match uu____58535 with
                   | (env1,free) ->
                       let uu____58559 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____58574 = free_type_vars env1 body  in
                             (env1, uu____58574)
                          in
                       (match uu____58559 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58511 with
           | (env1,free) ->
               let uu____58603 = free_type_vars env1 body  in
               FStar_List.append free uu____58603)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____58612 =
            FStar_List.fold_left
              (fun uu____58632  ->
                 fun binder  ->
                   match uu____58632 with
                   | (env1,free) ->
                       let uu____58652 = free_type_vars_b env1 binder  in
                       (match uu____58652 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58612 with
           | (env1,free) ->
               let uu____58683 = free_type_vars env1 body  in
               FStar_List.append free uu____58683)
      | FStar_Parser_AST.Project (t1,uu____58687) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____58698 = free_type_vars env rel  in
          let uu____58701 =
            let uu____58704 = free_type_vars env init1  in
            let uu____58707 =
              FStar_List.collect
                (fun uu____58716  ->
                   match uu____58716 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____58722 = free_type_vars env rel1  in
                       let uu____58725 =
                         let uu____58728 = free_type_vars env just  in
                         let uu____58731 = free_type_vars env next  in
                         FStar_List.append uu____58728 uu____58731  in
                       FStar_List.append uu____58722 uu____58725) steps
               in
            FStar_List.append uu____58704 uu____58707  in
          FStar_List.append uu____58698 uu____58701
      | FStar_Parser_AST.Abs uu____58734 -> []
      | FStar_Parser_AST.Let uu____58741 -> []
      | FStar_Parser_AST.LetOpen uu____58762 -> []
      | FStar_Parser_AST.If uu____58767 -> []
      | FStar_Parser_AST.QForall uu____58774 -> []
      | FStar_Parser_AST.QExists uu____58787 -> []
      | FStar_Parser_AST.Record uu____58800 -> []
      | FStar_Parser_AST.Match uu____58813 -> []
      | FStar_Parser_AST.TryWith uu____58828 -> []
      | FStar_Parser_AST.Bind uu____58843 -> []
      | FStar_Parser_AST.Quote uu____58850 -> []
      | FStar_Parser_AST.VQuote uu____58855 -> []
      | FStar_Parser_AST.Antiquote uu____58856 -> []
      | FStar_Parser_AST.Seq uu____58857 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____58911 =
        let uu____58912 = unparen t1  in uu____58912.FStar_Parser_AST.tm  in
      match uu____58911 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____58954 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____58979 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____58979  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59001 =
                     let uu____59002 =
                       let uu____59007 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59007)  in
                     FStar_Parser_AST.TAnnotated uu____59002  in
                   FStar_Parser_AST.mk_binder uu____59001
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
        let uu____59025 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____59025  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59047 =
                     let uu____59048 =
                       let uu____59053 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59053)  in
                     FStar_Parser_AST.TAnnotated uu____59048  in
                   FStar_Parser_AST.mk_binder uu____59047
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____59055 =
             let uu____59056 = unparen t  in uu____59056.FStar_Parser_AST.tm
              in
           match uu____59055 with
           | FStar_Parser_AST.Product uu____59057 -> t
           | uu____59064 ->
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
      | uu____59101 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____59112 -> true
    | FStar_Parser_AST.PatTvar (uu____59116,uu____59117) -> true
    | FStar_Parser_AST.PatVar (uu____59123,uu____59124) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____59131) -> is_var_pattern p1
    | uu____59144 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____59155) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____59168;
           FStar_Parser_AST.prange = uu____59169;_},uu____59170)
        -> true
    | uu____59182 -> false
  
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
    | uu____59198 -> p
  
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
            let uu____59271 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____59271 with
             | (name,args,uu____59314) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59364);
               FStar_Parser_AST.prange = uu____59365;_},args)
            when is_top_level1 ->
            let uu____59375 =
              let uu____59380 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____59380  in
            (uu____59375, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59402);
               FStar_Parser_AST.prange = uu____59403;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____59433 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____59492 -> acc
        | FStar_Parser_AST.PatName uu____59495 -> acc
        | FStar_Parser_AST.PatOp uu____59496 -> acc
        | FStar_Parser_AST.PatConst uu____59497 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____59514) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____59520) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____59529) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____59546 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____59546
        | FStar_Parser_AST.PatAscribed (pat,uu____59554) ->
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
    match projectee with | LocalBinder _0 -> true | uu____59636 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____59678 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_59727  ->
    match uu___432_59727 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____59734 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____59767  ->
    match uu____59767 with
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
      let uu____59849 =
        let uu____59866 =
          let uu____59869 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____59869  in
        let uu____59870 =
          let uu____59881 =
            let uu____59890 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____59890)  in
          [uu____59881]  in
        (uu____59866, uu____59870)  in
      FStar_Syntax_Syntax.Tm_app uu____59849  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____59939 =
        let uu____59956 =
          let uu____59959 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____59959  in
        let uu____59960 =
          let uu____59971 =
            let uu____59980 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____59980)  in
          [uu____59971]  in
        (uu____59956, uu____59960)  in
      FStar_Syntax_Syntax.Tm_app uu____59939  in
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
          let uu____60043 =
            let uu____60060 =
              let uu____60063 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____60063  in
            let uu____60064 =
              let uu____60075 =
                let uu____60084 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____60084)  in
              let uu____60092 =
                let uu____60103 =
                  let uu____60112 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____60112)  in
                [uu____60103]  in
              uu____60075 :: uu____60092  in
            (uu____60060, uu____60064)  in
          FStar_Syntax_Syntax.Tm_app uu____60043  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____60172 =
        let uu____60187 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____60206  ->
               match uu____60206 with
               | ({ FStar_Syntax_Syntax.ppname = uu____60217;
                    FStar_Syntax_Syntax.index = uu____60218;
                    FStar_Syntax_Syntax.sort = t;_},uu____60220)
                   ->
                   let uu____60228 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____60228) uu____60187
         in
      FStar_All.pipe_right bs uu____60172  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____60244 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____60262 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____60290 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____60311,uu____60312,bs,t,uu____60315,uu____60316)
                            ->
                            let uu____60325 = bs_univnames bs  in
                            let uu____60328 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____60325 uu____60328
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____60331,uu____60332,t,uu____60334,uu____60335,uu____60336)
                            -> FStar_Syntax_Free.univnames t
                        | uu____60343 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____60290 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_60352 = s  in
        let uu____60353 =
          let uu____60354 =
            let uu____60363 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____60381,bs,t,lids1,lids2) ->
                          let uu___1027_60394 = se  in
                          let uu____60395 =
                            let uu____60396 =
                              let uu____60413 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____60414 =
                                let uu____60415 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____60415 t  in
                              (lid, uvs, uu____60413, uu____60414, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____60396
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60395;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_60394.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_60394.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_60394.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_60394.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____60429,t,tlid,n1,lids1) ->
                          let uu___1037_60440 = se  in
                          let uu____60441 =
                            let uu____60442 =
                              let uu____60458 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____60458, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____60442  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60441;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_60440.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_60440.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_60440.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_60440.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____60462 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____60363, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____60354  in
        {
          FStar_Syntax_Syntax.sigel = uu____60353;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_60352.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_60352.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_60352.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_60352.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____60469,t) ->
        let uvs =
          let uu____60472 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____60472 FStar_Util.set_elements  in
        let uu___1046_60477 = s  in
        let uu____60478 =
          let uu____60479 =
            let uu____60486 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____60486)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____60479  in
        {
          FStar_Syntax_Syntax.sigel = uu____60478;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_60477.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_60477.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_60477.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_60477.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____60510 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____60513 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____60520) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60553,(FStar_Util.Inl t,uu____60555),uu____60556)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60603,(FStar_Util.Inr c,uu____60605),uu____60606)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____60653 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60654,(FStar_Util.Inl t,uu____60656),uu____60657) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60704,(FStar_Util.Inr c,uu____60706),uu____60707) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____60754 -> empty_set  in
          FStar_Util.set_union uu____60510 uu____60513  in
        let all_lb_univs =
          let uu____60758 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____60774 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____60774) empty_set)
             in
          FStar_All.pipe_right uu____60758 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_60784 = s  in
        let uu____60785 =
          let uu____60786 =
            let uu____60793 =
              let uu____60794 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_60806 = lb  in
                        let uu____60807 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____60810 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_60806.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____60807;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_60806.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____60810;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_60806.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_60806.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____60794)  in
            (uu____60793, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____60786  in
        {
          FStar_Syntax_Syntax.sigel = uu____60785;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_60784.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_60784.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_60784.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_60784.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____60819,fml) ->
        let uvs =
          let uu____60822 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____60822 FStar_Util.set_elements  in
        let uu___1112_60827 = s  in
        let uu____60828 =
          let uu____60829 =
            let uu____60836 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____60836)  in
          FStar_Syntax_Syntax.Sig_assume uu____60829  in
        {
          FStar_Syntax_Syntax.sigel = uu____60828;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_60827.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_60827.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_60827.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_60827.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____60838,bs,c,flags) ->
        let uvs =
          let uu____60847 =
            let uu____60850 = bs_univnames bs  in
            let uu____60853 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____60850 uu____60853  in
          FStar_All.pipe_right uu____60847 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_60861 = s  in
        let uu____60862 =
          let uu____60863 =
            let uu____60876 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____60877 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____60876, uu____60877, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____60863  in
        {
          FStar_Syntax_Syntax.sigel = uu____60862;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_60861.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_60861.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_60861.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_60861.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____60880 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_60888  ->
    match uu___433_60888 with
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
    | uu____60939 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____60960 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____60960)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____60986 =
      let uu____60987 = unparen t  in uu____60987.FStar_Parser_AST.tm  in
    match uu____60986 with
    | FStar_Parser_AST.Wild  ->
        let uu____60993 =
          let uu____60994 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____60994  in
        FStar_Util.Inr uu____60993
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____61007)) ->
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
             let uu____61098 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61098
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____61115 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61115
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____61131 =
               let uu____61137 =
                 let uu____61139 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____61139
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____61137)
                in
             FStar_Errors.raise_error uu____61131 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____61148 ->
        let rec aux t1 univargs =
          let uu____61185 =
            let uu____61186 = unparen t1  in uu____61186.FStar_Parser_AST.tm
             in
          match uu____61185 with
          | FStar_Parser_AST.App (t2,targ,uu____61194) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_61221  ->
                     match uu___434_61221 with
                     | FStar_Util.Inr uu____61228 -> true
                     | uu____61231 -> false) univargs
              then
                let uu____61239 =
                  let uu____61240 =
                    FStar_List.map
                      (fun uu___435_61250  ->
                         match uu___435_61250 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____61240  in
                FStar_Util.Inr uu____61239
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_61276  ->
                        match uu___436_61276 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____61286 -> failwith "impossible")
                     univargs
                    in
                 let uu____61290 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____61290)
          | uu____61306 ->
              let uu____61307 =
                let uu____61313 =
                  let uu____61315 =
                    let uu____61317 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____61317 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____61315  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61313)
                 in
              FStar_Errors.raise_error uu____61307 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____61332 ->
        let uu____61333 =
          let uu____61339 =
            let uu____61341 =
              let uu____61343 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____61343 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____61341  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61339)  in
        FStar_Errors.raise_error uu____61333 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____61384;_});
            FStar_Syntax_Syntax.pos = uu____61385;
            FStar_Syntax_Syntax.vars = uu____61386;_})::uu____61387
        ->
        let uu____61418 =
          let uu____61424 =
            let uu____61426 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____61426
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61424)  in
        FStar_Errors.raise_error uu____61418 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____61432 ->
        let uu____61451 =
          let uu____61457 =
            let uu____61459 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____61459
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61457)  in
        FStar_Errors.raise_error uu____61451 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____61472 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____61472) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____61500 = FStar_List.hd fields  in
        match uu____61500 with
        | (f,uu____61510) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____61522 =
                match uu____61522 with
                | (f',uu____61528) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____61530 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____61530
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
              (let uu____61540 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____61540);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____61903 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____61910 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____61911 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____61913,pats1) ->
              let aux out uu____61954 =
                match uu____61954 with
                | (p2,uu____61967) ->
                    let intersection =
                      let uu____61977 = pat_vars p2  in
                      FStar_Util.set_intersect uu____61977 out  in
                    let uu____61980 = FStar_Util.set_is_empty intersection
                       in
                    if uu____61980
                    then
                      let uu____61985 = pat_vars p2  in
                      FStar_Util.set_union out uu____61985
                    else
                      (let duplicate_bv =
                         let uu____61991 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____61991  in
                       let uu____61994 =
                         let uu____62000 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____62000)
                          in
                       FStar_Errors.raise_error uu____61994 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____62024 = pat_vars p1  in
            FStar_All.pipe_right uu____62024 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____62052 =
                let uu____62054 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____62054  in
              if uu____62052
              then ()
              else
                (let nonlinear_vars =
                   let uu____62063 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____62063  in
                 let first_nonlinear_var =
                   let uu____62067 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____62067  in
                 let uu____62070 =
                   let uu____62076 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____62076)  in
                 FStar_Errors.raise_error uu____62070 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____62104 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____62104 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____62121 ->
            let uu____62124 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____62124 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____62275 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____62299 =
              let uu____62300 =
                let uu____62301 =
                  let uu____62308 =
                    let uu____62309 =
                      let uu____62315 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____62315, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____62309  in
                  (uu____62308, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____62301  in
              {
                FStar_Parser_AST.pat = uu____62300;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____62299
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____62335 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____62338 = aux loc env1 p2  in
              match uu____62338 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_62427 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_62432 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_62432.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_62432.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_62427.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_62434 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_62439 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_62439.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_62439.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_62434.FStar_Syntax_Syntax.p)
                        }
                    | uu____62440 when top -> p4
                    | uu____62441 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____62446 =
                    match binder with
                    | LetBinder uu____62467 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____62492 = close_fun env1 t  in
                          desugar_term env1 uu____62492  in
                        let x1 =
                          let uu___1380_62494 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_62494.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_62494.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____62446 with
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
            let uu____62562 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____62562, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____62576 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62576, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62600 = resolvex loc env1 x  in
            (match uu____62600 with
             | (loc1,env2,xbv) ->
                 let uu____62629 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62629, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62652 = resolvex loc env1 x  in
            (match uu____62652 with
             | (loc1,env2,xbv) ->
                 let uu____62681 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62681, [], imp))
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
            let uu____62696 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62696, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____62726;_},args)
            ->
            let uu____62732 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____62793  ->
                     match uu____62793 with
                     | (loc1,env2,annots,args1) ->
                         let uu____62874 = aux loc1 env2 arg  in
                         (match uu____62874 with
                          | (loc2,env3,uu____62921,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____62732 with
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
                 let uu____63053 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63053, annots, false))
        | FStar_Parser_AST.PatApp uu____63071 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____63102 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____63153  ->
                     match uu____63153 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____63214 = aux loc1 env2 pat  in
                         (match uu____63214 with
                          | (loc2,env3,uu____63256,pat1,ans,uu____63259) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____63102 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____63356 =
                     let uu____63359 =
                       let uu____63366 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____63366  in
                     let uu____63367 =
                       let uu____63368 =
                         let uu____63382 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____63382, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____63368  in
                     FStar_All.pipe_left uu____63359 uu____63367  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____63416 =
                            let uu____63417 =
                              let uu____63431 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____63431, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____63417  in
                          FStar_All.pipe_left (pos_r r) uu____63416) pats1
                     uu____63356
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
            let uu____63489 =
              FStar_List.fold_left
                (fun uu____63549  ->
                   fun p2  ->
                     match uu____63549 with
                     | (loc1,env2,annots,pats) ->
                         let uu____63631 = aux loc1 env2 p2  in
                         (match uu____63631 with
                          | (loc2,env3,uu____63678,pat,ans,uu____63681) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____63489 with
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
                   | uu____63847 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____63850 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63850, annots, false))
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
                   (fun uu____63931  ->
                      match uu____63931 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____63961  ->
                      match uu____63961 with
                      | (f,uu____63967) ->
                          let uu____63968 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____63994  ->
                                    match uu____63994 with
                                    | (g,uu____64001) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____63968 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____64007,p2) ->
                               p2)))
               in
            let app =
              let uu____64014 =
                let uu____64015 =
                  let uu____64022 =
                    let uu____64023 =
                      let uu____64024 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____64024  in
                    FStar_Parser_AST.mk_pattern uu____64023
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____64022, args)  in
                FStar_Parser_AST.PatApp uu____64015  in
              FStar_Parser_AST.mk_pattern uu____64014
                p1.FStar_Parser_AST.prange
               in
            let uu____64027 = aux loc env1 app  in
            (match uu____64027 with
             | (env2,e,b,p2,annots,uu____64073) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____64113 =
                         let uu____64114 =
                           let uu____64128 =
                             let uu___1528_64129 = fv  in
                             let uu____64130 =
                               let uu____64133 =
                                 let uu____64134 =
                                   let uu____64141 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____64141)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____64134
                                  in
                               FStar_Pervasives_Native.Some uu____64133  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_64129.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_64129.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____64130
                             }  in
                           (uu____64128, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____64114  in
                       FStar_All.pipe_left pos uu____64113
                   | uu____64167 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____64253 = aux' true loc env1 p2  in
            (match uu____64253 with
             | (loc1,env2,var,p3,ans,uu____64297) ->
                 let uu____64312 =
                   FStar_List.fold_left
                     (fun uu____64361  ->
                        fun p4  ->
                          match uu____64361 with
                          | (loc2,env3,ps1) ->
                              let uu____64426 = aux' true loc2 env3 p4  in
                              (match uu____64426 with
                               | (loc3,env4,uu____64467,p5,ans1,uu____64470)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____64312 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____64631 ->
            let uu____64632 = aux' true loc env1 p1  in
            (match uu____64632 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____64729 = aux_maybe_or env p  in
      match uu____64729 with
      | (env1,b,pats) ->
          ((let uu____64784 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____64784
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
          let uu____64857 =
            let uu____64858 =
              let uu____64869 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____64869, (ty, tacopt))  in
            LetBinder uu____64858  in
          (env, uu____64857, [])  in
        let op_to_ident x =
          let uu____64886 =
            let uu____64892 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____64892, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____64886  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____64914 = op_to_ident x  in
              mklet uu____64914 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____64916) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____64922;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____64938 = op_to_ident x  in
              let uu____64939 = desugar_term env t  in
              mklet uu____64938 uu____64939 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____64941);
                 FStar_Parser_AST.prange = uu____64942;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____64962 = desugar_term env t  in
              mklet x uu____64962 tacopt1
          | uu____64963 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____64976 = desugar_data_pat env p  in
           match uu____64976 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____65005;
                      FStar_Syntax_Syntax.p = uu____65006;_},uu____65007)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____65020;
                      FStar_Syntax_Syntax.p = uu____65021;_},uu____65022)::[]
                     -> []
                 | uu____65035 -> p1  in
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
  fun uu____65043  ->
    fun env  ->
      fun pat  ->
        let uu____65047 = desugar_data_pat env pat  in
        match uu____65047 with | (env1,uu____65063,pat1) -> (env1, pat1)

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
      let uu____65085 = desugar_term_aq env e  in
      match uu____65085 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____65104 = desugar_typ_aq env e  in
      match uu____65104 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____65114  ->
        fun range  ->
          match uu____65114 with
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
              ((let uu____65136 =
                  let uu____65138 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____65138  in
                if uu____65136
                then
                  let uu____65141 =
                    let uu____65147 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____65147)  in
                  FStar_Errors.log_issue range uu____65141
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
                  let uu____65168 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____65168 range  in
                let lid1 =
                  let uu____65172 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____65172 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____65182 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____65182 range  in
                           let private_fv =
                             let uu____65184 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____65184 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_65185 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_65185.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_65185.FStar_Syntax_Syntax.vars)
                           }
                       | uu____65186 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65190 =
                        let uu____65196 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____65196)
                         in
                      FStar_Errors.raise_error uu____65190 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____65216 =
                  let uu____65223 =
                    let uu____65224 =
                      let uu____65241 =
                        let uu____65252 =
                          let uu____65261 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____65261)  in
                        [uu____65252]  in
                      (lid1, uu____65241)  in
                    FStar_Syntax_Syntax.Tm_app uu____65224  in
                  FStar_Syntax_Syntax.mk uu____65223  in
                uu____65216 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____65312 =
          let uu____65313 = unparen t  in uu____65313.FStar_Parser_AST.tm  in
        match uu____65312 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____65314; FStar_Ident.ident = uu____65315;
              FStar_Ident.nsstr = uu____65316; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____65321 ->
            let uu____65322 =
              let uu____65328 =
                let uu____65330 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____65330  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____65328)  in
            FStar_Errors.raise_error uu____65322 t.FStar_Parser_AST.range
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
          let uu___1725_65417 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_65417.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_65417.FStar_Syntax_Syntax.vars)
          }  in
        let uu____65420 =
          let uu____65421 = unparen top  in uu____65421.FStar_Parser_AST.tm
           in
        match uu____65420 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____65426 ->
            let uu____65435 = desugar_formula env top  in
            (uu____65435, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____65444 = desugar_formula env t  in (uu____65444, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____65453 = desugar_formula env t  in (uu____65453, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____65480 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____65480, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____65482 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____65482, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____65491 =
                let uu____65492 =
                  let uu____65499 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____65499, args)  in
                FStar_Parser_AST.Op uu____65492  in
              FStar_Parser_AST.mk_term uu____65491 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____65504 =
              let uu____65505 =
                let uu____65506 =
                  let uu____65513 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____65513, [e])  in
                FStar_Parser_AST.Op uu____65506  in
              FStar_Parser_AST.mk_term uu____65505 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____65504
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____65525 = FStar_Ident.text_of_id op_star  in
             uu____65525 = "*") &&
              (let uu____65530 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____65530 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____65547;_},t1::t2::[])
                  when
                  let uu____65553 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____65553 FStar_Option.isNone ->
                  let uu____65560 = flatten1 t1  in
                  FStar_List.append uu____65560 [t2]
              | uu____65563 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_65568 = top  in
              let uu____65569 =
                let uu____65570 =
                  let uu____65581 =
                    FStar_List.map (fun _65592  -> FStar_Util.Inr _65592)
                      terms
                     in
                  (uu____65581, rhs)  in
                FStar_Parser_AST.Sum uu____65570  in
              {
                FStar_Parser_AST.tm = uu____65569;
                FStar_Parser_AST.range =
                  (uu___1773_65568.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_65568.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____65600 =
              let uu____65601 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____65601  in
            (uu____65600, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____65607 =
              let uu____65613 =
                let uu____65615 =
                  let uu____65617 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____65617 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____65615  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____65613)
               in
            FStar_Errors.raise_error uu____65607 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____65632 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____65632 with
             | FStar_Pervasives_Native.None  ->
                 let uu____65639 =
                   let uu____65645 =
                     let uu____65647 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____65647
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____65645)
                    in
                 FStar_Errors.raise_error uu____65639
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____65662 =
                     let uu____65687 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____65749 = desugar_term_aq env t  in
                               match uu____65749 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____65687 FStar_List.unzip  in
                   (match uu____65662 with
                    | (args1,aqs) ->
                        let uu____65882 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____65882, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____65899)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____65916 =
              let uu___1802_65917 = top  in
              let uu____65918 =
                let uu____65919 =
                  let uu____65926 =
                    let uu___1804_65927 = top  in
                    let uu____65928 =
                      let uu____65929 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____65929  in
                    {
                      FStar_Parser_AST.tm = uu____65928;
                      FStar_Parser_AST.range =
                        (uu___1804_65927.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_65927.FStar_Parser_AST.level)
                    }  in
                  (uu____65926, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____65919  in
              {
                FStar_Parser_AST.tm = uu____65918;
                FStar_Parser_AST.range =
                  (uu___1802_65917.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_65917.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____65916
        | FStar_Parser_AST.Construct (n1,(a,uu____65937)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____65957 =
                let uu___1814_65958 = top  in
                let uu____65959 =
                  let uu____65960 =
                    let uu____65967 =
                      let uu___1816_65968 = top  in
                      let uu____65969 =
                        let uu____65970 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____65970  in
                      {
                        FStar_Parser_AST.tm = uu____65969;
                        FStar_Parser_AST.range =
                          (uu___1816_65968.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_65968.FStar_Parser_AST.level)
                      }  in
                    (uu____65967, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____65960  in
                {
                  FStar_Parser_AST.tm = uu____65959;
                  FStar_Parser_AST.range =
                    (uu___1814_65958.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_65958.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____65957))
        | FStar_Parser_AST.Construct (n1,(a,uu____65978)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____65995 =
              let uu___1825_65996 = top  in
              let uu____65997 =
                let uu____65998 =
                  let uu____66005 =
                    let uu___1827_66006 = top  in
                    let uu____66007 =
                      let uu____66008 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____66008  in
                    {
                      FStar_Parser_AST.tm = uu____66007;
                      FStar_Parser_AST.range =
                        (uu___1827_66006.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_66006.FStar_Parser_AST.level)
                    }  in
                  (uu____66005, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____65998  in
              {
                FStar_Parser_AST.tm = uu____65997;
                FStar_Parser_AST.range =
                  (uu___1825_65996.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_65996.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____65995
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66014; FStar_Ident.ident = uu____66015;
              FStar_Ident.nsstr = uu____66016; FStar_Ident.str = "Type0";_}
            ->
            let uu____66021 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____66021, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66022; FStar_Ident.ident = uu____66023;
              FStar_Ident.nsstr = uu____66024; FStar_Ident.str = "Type";_}
            ->
            let uu____66029 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____66029, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____66030; FStar_Ident.ident = uu____66031;
               FStar_Ident.nsstr = uu____66032; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____66052 =
              let uu____66053 =
                let uu____66054 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____66054  in
              mk1 uu____66053  in
            (uu____66052, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66055; FStar_Ident.ident = uu____66056;
              FStar_Ident.nsstr = uu____66057; FStar_Ident.str = "Effect";_}
            ->
            let uu____66062 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____66062, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66063; FStar_Ident.ident = uu____66064;
              FStar_Ident.nsstr = uu____66065; FStar_Ident.str = "True";_}
            ->
            let uu____66070 =
              let uu____66071 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66071
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66070, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66072; FStar_Ident.ident = uu____66073;
              FStar_Ident.nsstr = uu____66074; FStar_Ident.str = "False";_}
            ->
            let uu____66079 =
              let uu____66080 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66080
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66079, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____66083;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____66086 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____66086 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____66095 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____66095, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____66097 =
                    let uu____66099 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____66099 txt
                     in
                  failwith uu____66097))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66108 = desugar_name mk1 setpos env true l  in
              (uu____66108, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66117 = desugar_name mk1 setpos env true l  in
              (uu____66117, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____66135 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____66135 with
                | FStar_Pervasives_Native.Some uu____66145 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____66153 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____66153 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____66171 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____66192 =
                    let uu____66193 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____66193  in
                  (uu____66192, noaqs)
              | uu____66199 ->
                  let uu____66207 =
                    let uu____66213 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____66213)  in
                  FStar_Errors.raise_error uu____66207
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____66223 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____66223 with
              | FStar_Pervasives_Native.None  ->
                  let uu____66230 =
                    let uu____66236 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____66236)
                     in
                  FStar_Errors.raise_error uu____66230
                    top.FStar_Parser_AST.range
              | uu____66244 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____66248 = desugar_name mk1 setpos env true lid'  in
                  (uu____66248, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66270 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____66270 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____66289 ->
                       let uu____66296 =
                         FStar_Util.take
                           (fun uu____66320  ->
                              match uu____66320 with
                              | (uu____66326,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____66296 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____66371 =
                              let uu____66396 =
                                FStar_List.map
                                  (fun uu____66439  ->
                                     match uu____66439 with
                                     | (t,imp) ->
                                         let uu____66456 =
                                           desugar_term_aq env t  in
                                         (match uu____66456 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____66396
                                FStar_List.unzip
                               in
                            (match uu____66371 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____66599 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____66599, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____66618 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____66618 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____66629 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_66657  ->
                 match uu___437_66657 with
                 | FStar_Util.Inr uu____66663 -> true
                 | uu____66665 -> false) binders
            ->
            let terms =
              let uu____66674 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_66691  ->
                        match uu___438_66691 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____66697 -> failwith "Impossible"))
                 in
              FStar_List.append uu____66674 [t]  in
            let uu____66699 =
              let uu____66724 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____66781 = desugar_typ_aq env t1  in
                        match uu____66781 with
                        | (t',aq) ->
                            let uu____66792 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____66792, aq)))
                 in
              FStar_All.pipe_right uu____66724 FStar_List.unzip  in
            (match uu____66699 with
             | (targs,aqs) ->
                 let tup =
                   let uu____66902 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____66902
                    in
                 let uu____66911 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____66911, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____66938 =
              let uu____66955 =
                let uu____66962 =
                  let uu____66969 =
                    FStar_All.pipe_left
                      (fun _66978  -> FStar_Util.Inl _66978)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____66969]  in
                FStar_List.append binders uu____66962  in
              FStar_List.fold_left
                (fun uu____67023  ->
                   fun b  ->
                     match uu____67023 with
                     | (env1,tparams,typs) ->
                         let uu____67084 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____67099 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____67099)
                            in
                         (match uu____67084 with
                          | (xopt,t1) ->
                              let uu____67124 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____67133 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____67133)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____67124 with
                               | (env2,x) ->
                                   let uu____67153 =
                                     let uu____67156 =
                                       let uu____67159 =
                                         let uu____67160 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____67160
                                          in
                                       [uu____67159]  in
                                     FStar_List.append typs uu____67156  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_67186 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_67186.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_67186.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____67153)))) (env, [], [])
                uu____66955
               in
            (match uu____66938 with
             | (env1,uu____67214,targs) ->
                 let tup =
                   let uu____67237 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____67237
                    in
                 let uu____67238 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____67238, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____67257 = uncurry binders t  in
            (match uu____67257 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_67301 =
                   match uu___439_67301 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____67318 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____67318
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____67342 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____67342 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____67375 = aux env [] bs  in (uu____67375, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____67384 = desugar_binder env b  in
            (match uu____67384 with
             | (FStar_Pervasives_Native.None ,uu____67395) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____67410 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____67410 with
                  | ((x,uu____67426),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____67439 =
                        let uu____67440 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____67440  in
                      (uu____67439, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____67519 = FStar_Util.set_is_empty i  in
                    if uu____67519
                    then
                      let uu____67524 = FStar_Util.set_union acc set1  in
                      aux uu____67524 sets2
                    else
                      (let uu____67529 =
                         let uu____67530 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____67530  in
                       FStar_Pervasives_Native.Some uu____67529)
                 in
              let uu____67533 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____67533 sets  in
            ((let uu____67537 = check_disjoint bvss  in
              match uu____67537 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____67541 =
                    let uu____67547 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____67547)
                     in
                  let uu____67551 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____67541 uu____67551);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____67559 =
                FStar_List.fold_left
                  (fun uu____67579  ->
                     fun pat  ->
                       match uu____67579 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____67605,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____67615 =
                                  let uu____67618 = free_type_vars env1 t  in
                                  FStar_List.append uu____67618 ftvs  in
                                (env1, uu____67615)
                            | FStar_Parser_AST.PatAscribed
                                (uu____67623,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____67634 =
                                  let uu____67637 = free_type_vars env1 t  in
                                  let uu____67640 =
                                    let uu____67643 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____67643 ftvs  in
                                  FStar_List.append uu____67637 uu____67640
                                   in
                                (env1, uu____67634)
                            | uu____67648 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____67559 with
              | (uu____67657,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____67669 =
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
                    FStar_List.append uu____67669 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_67726 =
                    match uu___440_67726 with
                    | [] ->
                        let uu____67753 = desugar_term_aq env1 body  in
                        (match uu____67753 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____67790 =
                                       let uu____67791 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____67791
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____67790
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
                             let uu____67860 =
                               let uu____67863 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____67863  in
                             (uu____67860, aq))
                    | p::rest ->
                        let uu____67878 = desugar_binding_pat env1 p  in
                        (match uu____67878 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____67912)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____67927 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____67936 =
                               match b with
                               | LetBinder uu____67977 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____68046) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____68100 =
                                           let uu____68109 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____68109, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____68100
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____68171,uu____68172) ->
                                              let tup2 =
                                                let uu____68174 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68174
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68179 =
                                                  let uu____68186 =
                                                    let uu____68187 =
                                                      let uu____68204 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____68207 =
                                                        let uu____68218 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____68227 =
                                                          let uu____68238 =
                                                            let uu____68247 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____68247
                                                             in
                                                          [uu____68238]  in
                                                        uu____68218 ::
                                                          uu____68227
                                                         in
                                                      (uu____68204,
                                                        uu____68207)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____68187
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____68186
                                                   in
                                                uu____68179
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____68298 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____68298
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____68349,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____68351,pats)) ->
                                              let tupn =
                                                let uu____68396 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68396
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68409 =
                                                  let uu____68410 =
                                                    let uu____68427 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____68430 =
                                                      let uu____68441 =
                                                        let uu____68452 =
                                                          let uu____68461 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____68461
                                                           in
                                                        [uu____68452]  in
                                                      FStar_List.append args
                                                        uu____68441
                                                       in
                                                    (uu____68427,
                                                      uu____68430)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____68410
                                                   in
                                                mk1 uu____68409  in
                                              let p2 =
                                                let uu____68509 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____68509
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____68556 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____67936 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____68650,uu____68651,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____68673 =
                let uu____68674 = unparen e  in
                uu____68674.FStar_Parser_AST.tm  in
              match uu____68673 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____68684 ->
                  let uu____68685 = desugar_term_aq env e  in
                  (match uu____68685 with
                   | (head1,aq) ->
                       let uu____68698 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____68698, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____68705 ->
            let rec aux args aqs e =
              let uu____68782 =
                let uu____68783 = unparen e  in
                uu____68783.FStar_Parser_AST.tm  in
              match uu____68782 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____68801 = desugar_term_aq env t  in
                  (match uu____68801 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____68849 ->
                  let uu____68850 = desugar_term_aq env e  in
                  (match uu____68850 with
                   | (head1,aq) ->
                       let uu____68871 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____68871, (join_aqs (aq :: aqs))))
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
            let uu____68934 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____68934
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
            let uu____68986 = desugar_term_aq env t  in
            (match uu____68986 with
             | (tm,s) ->
                 let uu____68997 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____68997, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____69003 =
              let uu____69016 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____69016 then desugar_typ_aq else desugar_term_aq  in
            uu____69003 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____69075 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____69218  ->
                        match uu____69218 with
                        | (attr_opt,(p,def)) ->
                            let uu____69276 = is_app_pattern p  in
                            if uu____69276
                            then
                              let uu____69309 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____69309, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____69392 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____69392, def1)
                               | uu____69437 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____69475);
                                           FStar_Parser_AST.prange =
                                             uu____69476;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____69525 =
                                            let uu____69546 =
                                              let uu____69551 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69551  in
                                            (uu____69546, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____69525, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____69643) ->
                                        if top_level
                                        then
                                          let uu____69679 =
                                            let uu____69700 =
                                              let uu____69705 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69705  in
                                            (uu____69700, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____69679, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____69796 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____69829 =
                FStar_List.fold_left
                  (fun uu____69902  ->
                     fun uu____69903  ->
                       match (uu____69902, uu____69903) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____70011,uu____70012),uu____70013))
                           ->
                           let uu____70130 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____70156 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____70156 with
                                  | (env2,xx) ->
                                      let uu____70175 =
                                        let uu____70178 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____70178 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____70175))
                             | FStar_Util.Inr l ->
                                 let uu____70186 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____70186, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____70130 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____69829 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____70334 =
                    match uu____70334 with
                    | (attrs_opt,(uu____70370,args,result_t),def) ->
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
                                let uu____70458 = is_comp_type env1 t  in
                                if uu____70458
                                then
                                  ((let uu____70462 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____70472 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____70472))
                                       in
                                    match uu____70462 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____70479 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____70482 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____70482))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____70479
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
                          | uu____70493 ->
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
                              let uu____70508 =
                                let uu____70509 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____70509
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____70508
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
                  let uu____70590 = desugar_term_aq env' body  in
                  (match uu____70590 with
                   | (body1,aq) ->
                       let uu____70603 =
                         let uu____70606 =
                           let uu____70607 =
                             let uu____70621 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____70621)  in
                           FStar_Syntax_Syntax.Tm_let uu____70607  in
                         FStar_All.pipe_left mk1 uu____70606  in
                       (uu____70603, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____70696 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____70696 with
              | (env1,binder,pat1) ->
                  let uu____70718 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____70744 = desugar_term_aq env1 t2  in
                        (match uu____70744 with
                         | (body1,aq) ->
                             let fv =
                               let uu____70758 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____70758
                                 FStar_Pervasives_Native.None
                                in
                             let uu____70759 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____70759, aq))
                    | LocalBinder (x,uu____70792) ->
                        let uu____70793 = desugar_term_aq env1 t2  in
                        (match uu____70793 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____70807;
                                    FStar_Syntax_Syntax.p = uu____70808;_},uu____70809)::[]
                                   -> body1
                               | uu____70822 ->
                                   let uu____70825 =
                                     let uu____70832 =
                                       let uu____70833 =
                                         let uu____70856 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____70859 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____70856, uu____70859)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____70833
                                        in
                                     FStar_Syntax_Syntax.mk uu____70832  in
                                   uu____70825 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____70899 =
                               let uu____70902 =
                                 let uu____70903 =
                                   let uu____70917 =
                                     let uu____70920 =
                                       let uu____70921 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____70921]  in
                                     FStar_Syntax_Subst.close uu____70920
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____70917)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____70903  in
                               FStar_All.pipe_left mk1 uu____70902  in
                             (uu____70899, aq))
                     in
                  (match uu____70718 with | (tm,aq) -> (tm, aq))
               in
            let uu____70983 = FStar_List.hd lbs  in
            (match uu____70983 with
             | (attrs,(head_pat,defn)) ->
                 let uu____71027 = is_rec || (is_app_pattern head_pat)  in
                 if uu____71027
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____71043 =
                let uu____71044 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____71044  in
              mk1 uu____71043  in
            let uu____71045 = desugar_term_aq env t1  in
            (match uu____71045 with
             | (t1',aq1) ->
                 let uu____71056 = desugar_term_aq env t2  in
                 (match uu____71056 with
                  | (t2',aq2) ->
                      let uu____71067 = desugar_term_aq env t3  in
                      (match uu____71067 with
                       | (t3',aq3) ->
                           let uu____71078 =
                             let uu____71079 =
                               let uu____71080 =
                                 let uu____71103 =
                                   let uu____71120 =
                                     let uu____71135 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____71135,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____71149 =
                                     let uu____71166 =
                                       let uu____71181 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____71181,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____71166]  in
                                   uu____71120 :: uu____71149  in
                                 (t1', uu____71103)  in
                               FStar_Syntax_Syntax.Tm_match uu____71080  in
                             mk1 uu____71079  in
                           (uu____71078, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____71377 =
              match uu____71377 with
              | (pat,wopt,b) ->
                  let uu____71399 = desugar_match_pat env pat  in
                  (match uu____71399 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____71430 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____71430
                          in
                       let uu____71435 = desugar_term_aq env1 b  in
                       (match uu____71435 with
                        | (b1,aq) ->
                            let uu____71448 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____71448, aq)))
               in
            let uu____71453 = desugar_term_aq env e  in
            (match uu____71453 with
             | (e1,aq) ->
                 let uu____71464 =
                   let uu____71495 =
                     let uu____71528 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____71528 FStar_List.unzip  in
                   FStar_All.pipe_right uu____71495
                     (fun uu____71746  ->
                        match uu____71746 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____71464 with
                  | (brs,aqs) ->
                      let uu____71965 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____71965, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____71999 =
              let uu____72020 = is_comp_type env t  in
              if uu____72020
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____72075 = desugar_term_aq env t  in
                 match uu____72075 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____71999 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____72167 = desugar_term_aq env e  in
                 (match uu____72167 with
                  | (e1,aq) ->
                      let uu____72178 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____72178, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____72217,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____72260 = FStar_List.hd fields  in
              match uu____72260 with | (f,uu____72272) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____72318  ->
                        match uu____72318 with
                        | (g,uu____72325) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____72332,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____72346 =
                         let uu____72352 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____72352)
                          in
                       FStar_Errors.raise_error uu____72346
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
                  let uu____72363 =
                    let uu____72374 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____72405  ->
                              match uu____72405 with
                              | (f,uu____72415) ->
                                  let uu____72416 =
                                    let uu____72417 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____72417
                                     in
                                  (uu____72416, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____72374)  in
                  FStar_Parser_AST.Construct uu____72363
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____72435 =
                      let uu____72436 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____72436  in
                    FStar_Parser_AST.mk_term uu____72435
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____72438 =
                      let uu____72451 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____72481  ->
                                match uu____72481 with
                                | (f,uu____72491) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____72451)  in
                    FStar_Parser_AST.Record uu____72438  in
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
            let uu____72551 = desugar_term_aq env recterm1  in
            (match uu____72551 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____72567;
                         FStar_Syntax_Syntax.vars = uu____72568;_},args)
                      ->
                      let uu____72594 =
                        let uu____72595 =
                          let uu____72596 =
                            let uu____72613 =
                              let uu____72616 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____72617 =
                                let uu____72620 =
                                  let uu____72621 =
                                    let uu____72628 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____72628)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____72621
                                   in
                                FStar_Pervasives_Native.Some uu____72620  in
                              FStar_Syntax_Syntax.fvar uu____72616
                                FStar_Syntax_Syntax.delta_constant
                                uu____72617
                               in
                            (uu____72613, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____72596  in
                        FStar_All.pipe_left mk1 uu____72595  in
                      (uu____72594, s)
                  | uu____72657 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____72661 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____72661 with
              | (constrname,is_rec) ->
                  let uu____72680 = desugar_term_aq env e  in
                  (match uu____72680 with
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
                       let uu____72700 =
                         let uu____72701 =
                           let uu____72702 =
                             let uu____72719 =
                               let uu____72722 =
                                 let uu____72723 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____72723
                                  in
                               FStar_Syntax_Syntax.fvar uu____72722
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____72725 =
                               let uu____72736 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____72736]  in
                             (uu____72719, uu____72725)  in
                           FStar_Syntax_Syntax.Tm_app uu____72702  in
                         FStar_All.pipe_left mk1 uu____72701  in
                       (uu____72700, s))))
        | FStar_Parser_AST.NamedTyp (uu____72773,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____72783 =
              let uu____72784 = FStar_Syntax_Subst.compress tm  in
              uu____72784.FStar_Syntax_Syntax.n  in
            (match uu____72783 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72792 =
                   let uu___2520_72793 =
                     let uu____72794 =
                       let uu____72796 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____72796  in
                     FStar_Syntax_Util.exp_string uu____72794  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_72793.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_72793.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____72792, noaqs)
             | uu____72797 ->
                 let uu____72798 =
                   let uu____72804 =
                     let uu____72806 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____72806
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____72804)  in
                 FStar_Errors.raise_error uu____72798
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____72815 = desugar_term_aq env e  in
            (match uu____72815 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____72827 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____72827, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____72832 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____72833 =
              let uu____72834 =
                let uu____72841 = desugar_term env e  in (bv, uu____72841)
                 in
              [uu____72834]  in
            (uu____72832, uu____72833)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____72866 =
              let uu____72867 =
                let uu____72868 =
                  let uu____72875 = desugar_term env e  in (uu____72875, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____72868  in
              FStar_All.pipe_left mk1 uu____72867  in
            (uu____72866, noaqs)
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
              let uu____72904 =
                let uu____72905 =
                  let uu____72912 =
                    let uu____72913 =
                      let uu____72914 =
                        let uu____72923 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____72936 =
                          let uu____72937 =
                            let uu____72938 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____72938  in
                          FStar_Parser_AST.mk_term uu____72937
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____72923, uu____72936,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____72914  in
                    FStar_Parser_AST.mk_term uu____72913
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____72912)  in
                FStar_Parser_AST.Abs uu____72905  in
              FStar_Parser_AST.mk_term uu____72904
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
                   fun uu____72984  ->
                     match uu____72984 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____72988 =
                           let uu____72995 =
                             let uu____73000 = eta_and_annot rel2  in
                             (uu____73000, FStar_Parser_AST.Nothing)  in
                           let uu____73001 =
                             let uu____73008 =
                               let uu____73015 =
                                 let uu____73020 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____73020, FStar_Parser_AST.Nothing)  in
                               let uu____73021 =
                                 let uu____73028 =
                                   let uu____73033 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____73033, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____73028]  in
                               uu____73015 :: uu____73021  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____73008
                              in
                           uu____72995 :: uu____73001  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____72988
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____73055 =
                let uu____73062 =
                  let uu____73067 = FStar_Parser_AST.thunk e1  in
                  (uu____73067, FStar_Parser_AST.Nothing)  in
                [uu____73062]  in
              FStar_Parser_AST.mkApp finish1 uu____73055
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____73076 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____73077 = desugar_formula env top  in
            (uu____73077, noaqs)
        | uu____73078 ->
            let uu____73079 =
              let uu____73085 =
                let uu____73087 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____73087  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____73085)  in
            FStar_Errors.raise_error uu____73079 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____73097 -> false
    | uu____73107 -> true

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
           (fun uu____73145  ->
              match uu____73145 with
              | (a,imp) ->
                  let uu____73158 = desugar_term env a  in
                  arg_withimp_e imp uu____73158))

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
          let is_requires uu____73195 =
            match uu____73195 with
            | (t1,uu____73202) ->
                let uu____73203 =
                  let uu____73204 = unparen t1  in
                  uu____73204.FStar_Parser_AST.tm  in
                (match uu____73203 with
                 | FStar_Parser_AST.Requires uu____73206 -> true
                 | uu____73215 -> false)
             in
          let is_ensures uu____73227 =
            match uu____73227 with
            | (t1,uu____73234) ->
                let uu____73235 =
                  let uu____73236 = unparen t1  in
                  uu____73236.FStar_Parser_AST.tm  in
                (match uu____73235 with
                 | FStar_Parser_AST.Ensures uu____73238 -> true
                 | uu____73247 -> false)
             in
          let is_app head1 uu____73265 =
            match uu____73265 with
            | (t1,uu____73273) ->
                let uu____73274 =
                  let uu____73275 = unparen t1  in
                  uu____73275.FStar_Parser_AST.tm  in
                (match uu____73274 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____73278;
                        FStar_Parser_AST.level = uu____73279;_},uu____73280,uu____73281)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____73283 -> false)
             in
          let is_smt_pat uu____73295 =
            match uu____73295 with
            | (t1,uu____73302) ->
                let uu____73303 =
                  let uu____73304 = unparen t1  in
                  uu____73304.FStar_Parser_AST.tm  in
                (match uu____73303 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____73308);
                               FStar_Parser_AST.range = uu____73309;
                               FStar_Parser_AST.level = uu____73310;_},uu____73311)::uu____73312::[])
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
                               FStar_Parser_AST.range = uu____73361;
                               FStar_Parser_AST.level = uu____73362;_},uu____73363)::uu____73364::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____73397 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____73432 = head_and_args t1  in
            match uu____73432 with
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
                     let thunk_ens uu____73525 =
                       match uu____73525 with
                       | (e,i) ->
                           let uu____73536 = FStar_Parser_AST.thunk e  in
                           (uu____73536, i)
                        in
                     let fail_lemma uu____73548 =
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
                           let uu____73654 =
                             let uu____73661 =
                               let uu____73668 = thunk_ens ens  in
                               [uu____73668; nil_pat]  in
                             req_true :: uu____73661  in
                           unit_tm :: uu____73654
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____73715 =
                             let uu____73722 =
                               let uu____73729 = thunk_ens ens  in
                               [uu____73729; nil_pat]  in
                             req :: uu____73722  in
                           unit_tm :: uu____73715
                       | ens::smtpat::[] when
                           (((let uu____73778 = is_requires ens  in
                              Prims.op_Negation uu____73778) &&
                               (let uu____73781 = is_smt_pat ens  in
                                Prims.op_Negation uu____73781))
                              &&
                              (let uu____73784 = is_decreases ens  in
                               Prims.op_Negation uu____73784))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____73786 =
                             let uu____73793 =
                               let uu____73800 = thunk_ens ens  in
                               [uu____73800; smtpat]  in
                             req_true :: uu____73793  in
                           unit_tm :: uu____73786
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____73847 =
                             let uu____73854 =
                               let uu____73861 = thunk_ens ens  in
                               [uu____73861; nil_pat; dec]  in
                             req_true :: uu____73854  in
                           unit_tm :: uu____73847
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____73921 =
                             let uu____73928 =
                               let uu____73935 = thunk_ens ens  in
                               [uu____73935; smtpat; dec]  in
                             req_true :: uu____73928  in
                           unit_tm :: uu____73921
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____73995 =
                             let uu____74002 =
                               let uu____74009 = thunk_ens ens  in
                               [uu____74009; nil_pat; dec]  in
                             req :: uu____74002  in
                           unit_tm :: uu____73995
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____74069 =
                             let uu____74076 =
                               let uu____74083 = thunk_ens ens  in
                               [uu____74083; smtpat]  in
                             req :: uu____74076  in
                           unit_tm :: uu____74069
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____74148 =
                             let uu____74155 =
                               let uu____74162 = thunk_ens ens  in
                               [uu____74162; dec; smtpat]  in
                             req :: uu____74155  in
                           unit_tm :: uu____74148
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____74224 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____74224, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74252 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74252
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____74255 =
                       let uu____74262 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74262, [])  in
                     (uu____74255, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74280 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74280
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____74283 =
                       let uu____74290 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74290, [])  in
                     (uu____74283, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____74312 =
                       let uu____74319 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74319, [])  in
                     (uu____74312, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74342 when allow_type_promotion ->
                     let default_effect =
                       let uu____74344 = FStar_Options.ml_ish ()  in
                       if uu____74344
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____74350 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____74350
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____74357 =
                       let uu____74364 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74364, [])  in
                     (uu____74357, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74387 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____74406 = pre_process_comp_typ t  in
          match uu____74406 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____74458 =
                    let uu____74464 =
                      let uu____74466 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____74466
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____74464)
                     in
                  fail1 uu____74458)
               else ();
               (let is_universe uu____74482 =
                  match uu____74482 with
                  | (uu____74488,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____74490 = FStar_Util.take is_universe args  in
                match uu____74490 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____74549  ->
                           match uu____74549 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____74556 =
                      let uu____74571 = FStar_List.hd args1  in
                      let uu____74580 = FStar_List.tl args1  in
                      (uu____74571, uu____74580)  in
                    (match uu____74556 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____74635 =
                           let is_decrease uu____74674 =
                             match uu____74674 with
                             | (t1,uu____74685) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____74696;
                                         FStar_Syntax_Syntax.vars =
                                           uu____74697;_},uu____74698::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____74737 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____74635 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____74854  ->
                                        match uu____74854 with
                                        | (t1,uu____74864) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____74873,(arg,uu____74875)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____74914 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____74935 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____74947 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____74947
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____74954 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____74954
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____74964 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____74964
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____74971 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____74971
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____74978 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____74978
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____74985 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____74985
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____75006 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____75006
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
                                                    let uu____75097 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____75097
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
                                              | uu____75118 -> pat  in
                                            let uu____75119 =
                                              let uu____75130 =
                                                let uu____75141 =
                                                  let uu____75150 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____75150, aq)  in
                                                [uu____75141]  in
                                              ens :: uu____75130  in
                                            req :: uu____75119
                                        | uu____75191 -> rest2
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
        | uu____75223 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_75245 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_75245.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_75245.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_75287 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_75287.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_75287.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_75287.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____75350 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____75350)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____75363 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____75363 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_75373 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_75373.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_75373.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____75399 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____75413 =
                     let uu____75416 =
                       let uu____75417 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____75417]  in
                     no_annot_abs uu____75416 body2  in
                   FStar_All.pipe_left setpos uu____75413  in
                 let uu____75438 =
                   let uu____75439 =
                     let uu____75456 =
                       let uu____75459 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____75459
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____75461 =
                       let uu____75472 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____75472]  in
                     (uu____75456, uu____75461)  in
                   FStar_Syntax_Syntax.Tm_app uu____75439  in
                 FStar_All.pipe_left mk1 uu____75438)
        | uu____75511 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____75592 = q (rest, pats, body)  in
              let uu____75599 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____75592 uu____75599
                FStar_Parser_AST.Formula
               in
            let uu____75600 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____75600 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____75609 -> failwith "impossible"  in
      let uu____75613 =
        let uu____75614 = unparen f  in uu____75614.FStar_Parser_AST.tm  in
      match uu____75613 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____75627,uu____75628) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____75640,uu____75641) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75673 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____75673
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75709 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____75709
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____75753 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____75758 =
        FStar_List.fold_left
          (fun uu____75791  ->
             fun b  ->
               match uu____75791 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_75835 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_75835.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_75835.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_75835.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____75850 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____75850 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_75868 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_75868.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_75868.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____75869 =
                               let uu____75876 =
                                 let uu____75881 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____75881)  in
                               uu____75876 :: out  in
                             (env2, uu____75869))
                    | uu____75892 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____75758 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____75965 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____75965)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____75970 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____75970)
      | FStar_Parser_AST.TVariable x ->
          let uu____75974 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____75974)
      | FStar_Parser_AST.NoName t ->
          let uu____75978 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____75978)
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
      fun uu___441_75986  ->
        match uu___441_75986 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____76008 = FStar_Syntax_Syntax.null_binder k  in
            (uu____76008, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____76025 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____76025 with
             | (env1,a1) ->
                 let uu____76042 =
                   let uu____76049 = trans_aqual env1 imp  in
                   ((let uu___2962_76055 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_76055.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_76055.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____76049)
                    in
                 (uu____76042, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_76063  ->
      match uu___442_76063 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____76067 =
            let uu____76068 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____76068  in
          FStar_Pervasives_Native.Some uu____76067
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____76084) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____76086) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____76089 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____76107 = binder_ident b  in
         FStar_Common.list_of_option uu____76107) bs
  
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
               (fun uu___443_76144  ->
                  match uu___443_76144 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____76149 -> false))
           in
        let quals2 q =
          let uu____76163 =
            (let uu____76167 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____76167) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____76163
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____76184 = FStar_Ident.range_of_lid disc_name  in
                let uu____76185 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____76184;
                  FStar_Syntax_Syntax.sigquals = uu____76185;
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
            let uu____76225 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____76263  ->
                        match uu____76263 with
                        | (x,uu____76274) ->
                            let uu____76279 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____76279 with
                             | (field_name,uu____76287) ->
                                 let only_decl =
                                   ((let uu____76292 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____76292)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____76294 =
                                        let uu____76296 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____76296.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____76294)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____76314 =
                                       FStar_List.filter
                                         (fun uu___444_76318  ->
                                            match uu___444_76318 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____76321 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____76314
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_76336  ->
                                             match uu___445_76336 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____76341 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____76344 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____76344;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____76351 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____76351
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____76362 =
                                        let uu____76367 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____76367  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____76362;
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
                                      let uu____76371 =
                                        let uu____76372 =
                                          let uu____76379 =
                                            let uu____76382 =
                                              let uu____76383 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____76383
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____76382]  in
                                          ((false, [lb]), uu____76379)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____76372
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____76371;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____76225 FStar_List.flatten
  
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
            (lid,uu____76432,t,uu____76434,n1,uu____76436) when
            let uu____76443 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____76443 ->
            let uu____76445 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____76445 with
             | (formals,uu____76463) ->
                 (match formals with
                  | [] -> []
                  | uu____76492 ->
                      let filter_records uu___446_76508 =
                        match uu___446_76508 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____76511,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____76523 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____76525 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____76525 with
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
                      let uu____76537 = FStar_Util.first_N n1 formals  in
                      (match uu____76537 with
                       | (uu____76566,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____76600 -> []
  
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
                    let uu____76679 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____76679
                    then
                      let uu____76685 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____76685
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____76689 =
                      let uu____76694 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____76694  in
                    let uu____76695 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____76701 =
                          let uu____76704 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____76704  in
                        FStar_Syntax_Util.arrow typars uu____76701
                      else FStar_Syntax_Syntax.tun  in
                    let uu____76709 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____76689;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____76695;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____76709;
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
          let tycon_id uu___447_76763 =
            match uu___447_76763 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____76765,uu____76766) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____76776,uu____76777,uu____76778) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____76788,uu____76789,uu____76790) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____76820,uu____76821,uu____76822) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____76868) ->
                let uu____76869 =
                  let uu____76870 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76870  in
                FStar_Parser_AST.mk_term uu____76869 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____76872 =
                  let uu____76873 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76873  in
                FStar_Parser_AST.mk_term uu____76872 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____76875) ->
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
              | uu____76906 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____76914 =
                     let uu____76915 =
                       let uu____76922 = binder_to_term b  in
                       (out, uu____76922, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____76915  in
                   FStar_Parser_AST.mk_term uu____76914
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_76934 =
            match uu___448_76934 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____76991  ->
                       match uu____76991 with
                       | (x,t,uu____77002) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____77008 =
                    let uu____77009 =
                      let uu____77010 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____77010  in
                    FStar_Parser_AST.mk_term uu____77009
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____77008 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____77017 = binder_idents parms  in id1 ::
                    uu____77017
                   in
                (FStar_List.iter
                   (fun uu____77035  ->
                      match uu____77035 with
                      | (f,uu____77045,uu____77046) ->
                          let uu____77051 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____77051
                          then
                            let uu____77056 =
                              let uu____77062 =
                                let uu____77064 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____77064
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____77062)
                               in
                            FStar_Errors.raise_error uu____77056
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____77070 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____77097  ->
                            match uu____77097 with
                            | (x,uu____77107,uu____77108) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____77070)))
            | uu____77166 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_77206 =
            match uu___449_77206 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____77230 = typars_of_binders _env binders  in
                (match uu____77230 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____77266 =
                         let uu____77267 =
                           let uu____77268 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____77268  in
                         FStar_Parser_AST.mk_term uu____77267
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____77266 binders  in
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
            | uu____77279 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____77322 =
              FStar_List.fold_left
                (fun uu____77356  ->
                   fun uu____77357  ->
                     match (uu____77356, uu____77357) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____77426 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____77426 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____77322 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____77517 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____77517
                | uu____77518 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____77526 = desugar_abstract_tc quals env [] tc  in
              (match uu____77526 with
               | (uu____77539,uu____77540,se,uu____77542) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____77545,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____77564 =
                                 let uu____77566 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____77566  in
                               if uu____77564
                               then
                                 let uu____77569 =
                                   let uu____77575 =
                                     let uu____77577 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____77577
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____77575)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____77569
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
                           | uu____77590 ->
                               let uu____77591 =
                                 let uu____77598 =
                                   let uu____77599 =
                                     let uu____77614 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____77614)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____77599
                                    in
                                 FStar_Syntax_Syntax.mk uu____77598  in
                               uu____77591 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_77630 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_77630.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_77630.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_77630.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____77631 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____77635 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____77635
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____77648 = typars_of_binders env binders  in
              (match uu____77648 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____77682 =
                           FStar_Util.for_some
                             (fun uu___450_77685  ->
                                match uu___450_77685 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____77688 -> false) quals
                            in
                         if uu____77682
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____77696 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____77696
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____77701 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_77707  ->
                               match uu___451_77707 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____77710 -> false))
                        in
                     if uu____77701
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____77724 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____77724
                     then
                       let uu____77730 =
                         let uu____77737 =
                           let uu____77738 = unparen t  in
                           uu____77738.FStar_Parser_AST.tm  in
                         match uu____77737 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____77759 =
                               match FStar_List.rev args with
                               | (last_arg,uu____77789)::args_rev ->
                                   let uu____77801 =
                                     let uu____77802 = unparen last_arg  in
                                     uu____77802.FStar_Parser_AST.tm  in
                                   (match uu____77801 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____77830 -> ([], args))
                               | uu____77839 -> ([], args)  in
                             (match uu____77759 with
                              | (cattributes,args1) ->
                                  let uu____77878 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____77878))
                         | uu____77889 -> (t, [])  in
                       match uu____77730 with
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
                                  (fun uu___452_77912  ->
                                     match uu___452_77912 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____77915 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____77924)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____77948 = tycon_record_as_variant trec  in
              (match uu____77948 with
               | (t,fs) ->
                   let uu____77965 =
                     let uu____77968 =
                       let uu____77969 =
                         let uu____77978 =
                           let uu____77981 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____77981  in
                         (uu____77978, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____77969  in
                     uu____77968 :: quals  in
                   desugar_tycon env d uu____77965 [t])
          | uu____77986::uu____77987 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____78157 = et  in
                match uu____78157 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____78387 ->
                         let trec = tc  in
                         let uu____78411 = tycon_record_as_variant trec  in
                         (match uu____78411 with
                          | (t,fs) ->
                              let uu____78471 =
                                let uu____78474 =
                                  let uu____78475 =
                                    let uu____78484 =
                                      let uu____78487 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____78487  in
                                    (uu____78484, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____78475
                                   in
                                uu____78474 :: quals1  in
                              collect_tcs uu____78471 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____78577 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78577 with
                          | (env2,uu____78638,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____78791 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78791 with
                          | (env2,uu____78852,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____78980 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____79030 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____79030 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_79545  ->
                             match uu___454_79545 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____79611,uu____79612);
                                    FStar_Syntax_Syntax.sigrng = uu____79613;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____79614;
                                    FStar_Syntax_Syntax.sigmeta = uu____79615;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79616;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____79680 =
                                     typars_of_binders env1 binders  in
                                   match uu____79680 with
                                   | (env2,tpars1) ->
                                       let uu____79707 =
                                         push_tparams env2 tpars1  in
                                       (match uu____79707 with
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
                                 let uu____79736 =
                                   let uu____79755 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____79755)
                                    in
                                 [uu____79736]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____79815);
                                    FStar_Syntax_Syntax.sigrng = uu____79816;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____79818;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79819;_},constrs,tconstr,quals1)
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
                                 let uu____79920 = push_tparams env1 tpars
                                    in
                                 (match uu____79920 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____79987  ->
                                             match uu____79987 with
                                             | (x,uu____79999) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____80004 =
                                        let uu____80031 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____80141  ->
                                                  match uu____80141 with
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
                                                        let uu____80201 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____80201
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
                                                                uu___453_80212
                                                                 ->
                                                                match uu___453_80212
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____80224
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____80232 =
                                                        let uu____80251 =
                                                          let uu____80252 =
                                                            let uu____80253 =
                                                              let uu____80269
                                                                =
                                                                let uu____80270
                                                                  =
                                                                  let uu____80273
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____80273
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____80270
                                                                 in
                                                              (name, univs1,
                                                                uu____80269,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____80253
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____80252;
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
                                                          uu____80251)
                                                         in
                                                      (name, uu____80232)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____80031
                                         in
                                      (match uu____80004 with
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
                             | uu____80489 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80617  ->
                             match uu____80617 with
                             | (name_doc,uu____80643,uu____80644) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80716  ->
                             match uu____80716 with
                             | (uu____80735,uu____80736,se) -> se))
                      in
                   let uu____80762 =
                     let uu____80769 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____80769 rng
                      in
                   (match uu____80762 with
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
                               (fun uu____80831  ->
                                  match uu____80831 with
                                  | (uu____80852,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____80900,tps,k,uu____80903,constrs)
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
                                      let uu____80924 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____80939 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____80956,uu____80957,uu____80958,uu____80959,uu____80960)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____80967
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____80939
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____80971 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_80978 
                                                          ->
                                                          match uu___455_80978
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____80980 ->
                                                              true
                                                          | uu____80990 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____80971))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____80924
                                  | uu____80992 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____81009  ->
                                 match uu____81009 with
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
      let uu____81054 =
        FStar_List.fold_left
          (fun uu____81089  ->
             fun b  ->
               match uu____81089 with
               | (env1,binders1) ->
                   let uu____81133 = desugar_binder env1 b  in
                   (match uu____81133 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____81156 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____81156 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____81209 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____81054 with
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
          let uu____81313 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_81320  ->
                    match uu___456_81320 with
                    | FStar_Syntax_Syntax.Reflectable uu____81322 -> true
                    | uu____81324 -> false))
             in
          if uu____81313
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____81329 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____81329
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
      let uu____81370 = FStar_Syntax_Util.head_and_args at1  in
      match uu____81370 with
      | (hd1,args) ->
          let uu____81423 =
            let uu____81438 =
              let uu____81439 = FStar_Syntax_Subst.compress hd1  in
              uu____81439.FStar_Syntax_Syntax.n  in
            (uu____81438, args)  in
          (match uu____81423 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____81464)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____81499 =
                 let uu____81504 =
                   let uu____81513 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____81513 a1  in
                 uu____81504 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____81499 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____81543 =
                      let uu____81552 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____81552, b)  in
                    FStar_Pervasives_Native.Some uu____81543
                | uu____81569 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____81623) when
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
           | uu____81658 -> FStar_Pervasives_Native.None)
  
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
                  let uu____81830 = desugar_binders monad_env eff_binders  in
                  match uu____81830 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____81870 =
                          let uu____81872 =
                            let uu____81881 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____81881  in
                          FStar_List.length uu____81872  in
                        uu____81870 = (Prims.parse_int "1")  in
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
                            (uu____81965,uu____81966,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____81968,uu____81969,uu____81970),uu____81971)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____82008 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____82011 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____82023 = name_of_eff_decl decl  in
                             FStar_List.mem uu____82023 mandatory_members)
                          eff_decls
                         in
                      (match uu____82011 with
                       | (mandatory_members_decls,actions) ->
                           let uu____82042 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____82071  ->
                                     fun decl  ->
                                       match uu____82071 with
                                       | (env2,out) ->
                                           let uu____82091 =
                                             desugar_decl env2 decl  in
                                           (match uu____82091 with
                                            | (env3,ses) ->
                                                let uu____82104 =
                                                  let uu____82107 =
                                                    FStar_List.hd ses  in
                                                  uu____82107 :: out  in
                                                (env3, uu____82104)))
                                  (env1, []))
                              in
                           (match uu____82042 with
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
                                              (uu____82176,uu____82177,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82180,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____82181,(def,uu____82183)::
                                                      (cps_type,uu____82185)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____82186;
                                                   FStar_Parser_AST.level =
                                                     uu____82187;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____82243 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82243 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82281 =
                                                     let uu____82282 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82283 =
                                                       let uu____82284 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82284
                                                        in
                                                     let uu____82291 =
                                                       let uu____82292 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82292
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82282;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82283;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____82291
                                                     }  in
                                                   (uu____82281, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____82301,uu____82302,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82305,defn),doc1)::[])
                                              when for_free ->
                                              let uu____82344 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82344 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82382 =
                                                     let uu____82383 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82384 =
                                                       let uu____82385 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82385
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82383;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82384;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____82382, doc1))
                                          | uu____82394 ->
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
                                    let uu____82430 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____82430
                                     in
                                  let uu____82432 =
                                    let uu____82433 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____82433
                                     in
                                  ([], uu____82432)  in
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
                                      let uu____82451 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____82451)  in
                                    let uu____82458 =
                                      let uu____82459 =
                                        let uu____82460 =
                                          let uu____82461 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____82461
                                           in
                                        let uu____82471 = lookup1 "return"
                                           in
                                        let uu____82473 = lookup1 "bind"  in
                                        let uu____82475 =
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
                                            uu____82460;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____82471;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____82473;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____82475
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____82459
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____82458;
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
                                         (fun uu___457_82483  ->
                                            match uu___457_82483 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____82486 -> true
                                            | uu____82488 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____82503 =
                                       let uu____82504 =
                                         let uu____82505 =
                                           lookup1 "return_wp"  in
                                         let uu____82507 = lookup1 "bind_wp"
                                            in
                                         let uu____82509 =
                                           lookup1 "if_then_else"  in
                                         let uu____82511 = lookup1 "ite_wp"
                                            in
                                         let uu____82513 = lookup1 "stronger"
                                            in
                                         let uu____82515 = lookup1 "close_wp"
                                            in
                                         let uu____82517 = lookup1 "assert_p"
                                            in
                                         let uu____82519 = lookup1 "assume_p"
                                            in
                                         let uu____82521 = lookup1 "null_wp"
                                            in
                                         let uu____82523 = lookup1 "trivial"
                                            in
                                         let uu____82525 =
                                           if rr
                                           then
                                             let uu____82527 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____82527
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____82545 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____82550 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____82555 =
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
                                             uu____82505;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____82507;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____82509;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____82511;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____82513;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____82515;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____82517;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____82519;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____82521;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____82523;
                                           FStar_Syntax_Syntax.repr =
                                             uu____82525;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____82545;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____82550;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____82555
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____82504
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____82503;
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
                                          fun uu____82581  ->
                                            match uu____82581 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____82595 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____82595
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
                let uu____82619 = desugar_binders env1 eff_binders  in
                match uu____82619 with
                | (env2,binders) ->
                    let uu____82656 =
                      let uu____82667 = head_and_args defn  in
                      match uu____82667 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____82704 ->
                                let uu____82705 =
                                  let uu____82711 =
                                    let uu____82713 =
                                      let uu____82715 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____82715 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____82713  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____82711)
                                   in
                                FStar_Errors.raise_error uu____82705
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____82721 =
                            match FStar_List.rev args with
                            | (last_arg,uu____82751)::args_rev ->
                                let uu____82763 =
                                  let uu____82764 = unparen last_arg  in
                                  uu____82764.FStar_Parser_AST.tm  in
                                (match uu____82763 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____82792 -> ([], args))
                            | uu____82801 -> ([], args)  in
                          (match uu____82721 with
                           | (cattributes,args1) ->
                               let uu____82844 = desugar_args env2 args1  in
                               let uu____82845 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____82844, uu____82845))
                       in
                    (match uu____82656 with
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
                          (let uu____82885 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____82885 with
                           | (ed_binders,uu____82899,ed_binders_opening) ->
                               let sub' shift_n uu____82918 =
                                 match uu____82918 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____82933 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____82933 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____82937 =
                                       let uu____82938 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____82938)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____82937
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____82959 =
                                   let uu____82960 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____82960
                                    in
                                 let uu____82975 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____82976 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____82977 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____82978 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____82979 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____82980 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____82981 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____82982 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____82983 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____82984 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____82985 =
                                   let uu____82986 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____82986
                                    in
                                 let uu____83001 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____83002 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____83003 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____83019 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____83020 =
                                          let uu____83021 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83021
                                           in
                                        let uu____83042 =
                                          let uu____83043 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83043
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____83019;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____83020;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____83042
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
                                     uu____82959;
                                   FStar_Syntax_Syntax.ret_wp = uu____82975;
                                   FStar_Syntax_Syntax.bind_wp = uu____82976;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____82977;
                                   FStar_Syntax_Syntax.ite_wp = uu____82978;
                                   FStar_Syntax_Syntax.stronger = uu____82979;
                                   FStar_Syntax_Syntax.close_wp = uu____82980;
                                   FStar_Syntax_Syntax.assert_p = uu____82981;
                                   FStar_Syntax_Syntax.assume_p = uu____82982;
                                   FStar_Syntax_Syntax.null_wp = uu____82983;
                                   FStar_Syntax_Syntax.trivial = uu____82984;
                                   FStar_Syntax_Syntax.repr = uu____82985;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____83001;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____83002;
                                   FStar_Syntax_Syntax.actions = uu____83003;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____83067 =
                                     let uu____83069 =
                                       let uu____83078 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____83078
                                        in
                                     FStar_List.length uu____83069  in
                                   uu____83067 = (Prims.parse_int "1")  in
                                 let uu____83111 =
                                   let uu____83114 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____83114 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____83111;
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
                                             let uu____83138 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____83138
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____83140 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____83140
                                 then
                                   let reflect_lid =
                                     let uu____83147 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____83147
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
    let uu____83159 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____83159 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____83244 ->
              let uu____83247 =
                let uu____83249 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____83249
                 in
              Prims.op_Hat "\n  " uu____83247
          | uu____83252 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____83271  ->
               match uu____83271 with
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
          let uu____83316 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____83316
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____83319 =
          let uu____83330 = FStar_Syntax_Syntax.as_arg arg  in [uu____83330]
           in
        FStar_Syntax_Util.mk_app fv uu____83319

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83361 = desugar_decl_noattrs env d  in
      match uu____83361 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____83379 = mk_comment_attr d  in uu____83379 :: attrs1  in
          let uu____83380 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_83390 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_83390.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_83390.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_83390.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_83390.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_83393 = sigelt  in
                      let uu____83394 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____83400 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____83400) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_83393.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_83393.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_83393.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_83393.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____83394
                      })) sigelts
             in
          (env1, uu____83380)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83426 = desugar_decl_aux env d  in
      match uu____83426 with
      | (env1,ses) ->
          let uu____83437 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____83437)

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
      | FStar_Parser_AST.Fsdoc uu____83465 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____83470 = FStar_Syntax_DsEnv.iface env  in
          if uu____83470
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____83485 =
               let uu____83487 =
                 let uu____83489 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____83490 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____83489
                   uu____83490
                  in
               Prims.op_Negation uu____83487  in
             if uu____83485
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____83504 =
                  let uu____83506 =
                    let uu____83508 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____83508 lid  in
                  Prims.op_Negation uu____83506  in
                if uu____83504
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____83522 =
                     let uu____83524 =
                       let uu____83526 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____83526
                         lid
                        in
                     Prims.op_Negation uu____83524  in
                   if uu____83522
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____83544 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____83544, [])
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
              | (FStar_Parser_AST.TyconRecord uu____83585,uu____83586)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____83625 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____83652  ->
                 match uu____83652 with | (x,uu____83660) -> x) tcs
             in
          let uu____83665 =
            let uu____83670 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____83670 tcs1  in
          (match uu____83665 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____83687 =
                   let uu____83688 =
                     let uu____83695 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____83695  in
                   [uu____83688]  in
                 let uu____83708 =
                   let uu____83711 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____83714 =
                     let uu____83725 =
                       let uu____83734 =
                         let uu____83735 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____83735  in
                       FStar_Syntax_Syntax.as_arg uu____83734  in
                     [uu____83725]  in
                   FStar_Syntax_Util.mk_app uu____83711 uu____83714  in
                 FStar_Syntax_Util.abs uu____83687 uu____83708
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____83775,id1))::uu____83777 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____83780::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____83784 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____83784 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____83790 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____83790]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____83811) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____83821,uu____83822,uu____83823,uu____83824,uu____83825)
                     ->
                     let uu____83834 =
                       let uu____83835 =
                         let uu____83836 =
                           let uu____83843 = mkclass lid  in
                           (meths, uu____83843)  in
                         FStar_Syntax_Syntax.Sig_splice uu____83836  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____83835;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____83834]
                 | uu____83846 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____83880;
                    FStar_Parser_AST.prange = uu____83881;_},uu____83882)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____83892;
                    FStar_Parser_AST.prange = uu____83893;_},uu____83894)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____83910;
                         FStar_Parser_AST.prange = uu____83911;_},uu____83912);
                    FStar_Parser_AST.prange = uu____83913;_},uu____83914)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____83936;
                         FStar_Parser_AST.prange = uu____83937;_},uu____83938);
                    FStar_Parser_AST.prange = uu____83939;_},uu____83940)::[]
                   -> false
               | (p,uu____83969)::[] ->
                   let uu____83978 = is_app_pattern p  in
                   Prims.op_Negation uu____83978
               | uu____83980 -> false)
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
            let uu____84055 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____84055 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____84068 =
                     let uu____84069 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____84069.FStar_Syntax_Syntax.n  in
                   match uu____84068 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____84079) ->
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
                         | uu____84115::uu____84116 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____84119 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_84135  ->
                                     match uu___458_84135 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____84138;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84139;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84140;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84141;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84142;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84143;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84144;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84156;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84157;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84158;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84159;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84160;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84161;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____84175 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____84208  ->
                                   match uu____84208 with
                                   | (uu____84222,(uu____84223,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____84175
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____84243 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____84243
                         then
                           let uu____84249 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_84264 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_84266 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_84266.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_84266.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_84264.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_84264.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_84264.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_84264.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_84264.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_84264.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____84249)
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
                   | uu____84296 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____84304 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____84323 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____84304 with
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
                       let uu___4019_84360 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_84360.FStar_Parser_AST.prange)
                       }
                   | uu____84367 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_84374 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_84374.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_84374.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_84374.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____84410 id1 =
                   match uu____84410 with
                   | (env1,ses) ->
                       let main =
                         let uu____84431 =
                           let uu____84432 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____84432  in
                         FStar_Parser_AST.mk_term uu____84431
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
                       let uu____84482 = desugar_decl env1 id_decl  in
                       (match uu____84482 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____84500 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____84500 FStar_Util.set_elements
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
            let uu____84524 = close_fun env t  in
            desugar_term env uu____84524  in
          let quals1 =
            let uu____84528 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____84528
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____84540 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____84540;
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
                let uu____84554 =
                  let uu____84563 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____84563]  in
                let uu____84582 =
                  let uu____84585 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____84585
                   in
                FStar_Syntax_Util.arrow uu____84554 uu____84582
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
            let uu____84640 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____84640 with
            | FStar_Pervasives_Native.None  ->
                let uu____84643 =
                  let uu____84649 =
                    let uu____84651 =
                      let uu____84653 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____84653 " not found"  in
                    Prims.op_Hat "Effect name " uu____84651  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____84649)  in
                FStar_Errors.raise_error uu____84643
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____84661 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____84679 =
                  let uu____84682 =
                    let uu____84683 = desugar_term env t  in
                    ([], uu____84683)  in
                  FStar_Pervasives_Native.Some uu____84682  in
                (uu____84679, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____84696 =
                  let uu____84699 =
                    let uu____84700 = desugar_term env wp  in
                    ([], uu____84700)  in
                  FStar_Pervasives_Native.Some uu____84699  in
                let uu____84707 =
                  let uu____84710 =
                    let uu____84711 = desugar_term env t  in
                    ([], uu____84711)  in
                  FStar_Pervasives_Native.Some uu____84710  in
                (uu____84696, uu____84707)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____84723 =
                  let uu____84726 =
                    let uu____84727 = desugar_term env t  in
                    ([], uu____84727)  in
                  FStar_Pervasives_Native.Some uu____84726  in
                (FStar_Pervasives_Native.None, uu____84723)
             in
          (match uu____84661 with
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
            let uu____84761 =
              let uu____84762 =
                let uu____84769 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____84769, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____84762  in
            {
              FStar_Syntax_Syntax.sigel = uu____84761;
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
      let uu____84796 =
        FStar_List.fold_left
          (fun uu____84816  ->
             fun d  ->
               match uu____84816 with
               | (env1,sigelts) ->
                   let uu____84836 = desugar_decl env1 d  in
                   (match uu____84836 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____84796 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_84881 =
            match uu___460_84881 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____84895,FStar_Syntax_Syntax.Sig_let uu____84896) ->
                     let uu____84909 =
                       let uu____84912 =
                         let uu___4152_84913 = se2  in
                         let uu____84914 =
                           let uu____84917 =
                             FStar_List.filter
                               (fun uu___459_84931  ->
                                  match uu___459_84931 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____84936;
                                           FStar_Syntax_Syntax.vars =
                                             uu____84937;_},uu____84938);
                                      FStar_Syntax_Syntax.pos = uu____84939;
                                      FStar_Syntax_Syntax.vars = uu____84940;_}
                                      when
                                      let uu____84967 =
                                        let uu____84969 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____84969
                                         in
                                      uu____84967 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____84973 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____84917
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_84913.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_84913.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_84913.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_84913.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____84914
                         }  in
                       uu____84912 :: se1 :: acc  in
                     forward uu____84909 sigelts1
                 | uu____84979 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____84987 = forward [] sigelts  in (env1, uu____84987)
  
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
          | (FStar_Pervasives_Native.None ,uu____85052) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____85056;
               FStar_Syntax_Syntax.exports = uu____85057;
               FStar_Syntax_Syntax.is_interface = uu____85058;_},FStar_Parser_AST.Module
             (current_lid,uu____85060)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____85069) ->
              let uu____85072 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____85072
           in
        let uu____85077 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____85119 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85119, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____85141 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85141, mname, decls, false)
           in
        match uu____85077 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____85183 = desugar_decls env2 decls  in
            (match uu____85183 with
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
          let uu____85251 =
            (FStar_Options.interactive ()) &&
              (let uu____85254 =
                 let uu____85256 =
                   let uu____85258 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____85258  in
                 FStar_Util.get_file_extension uu____85256  in
               FStar_List.mem uu____85254 ["fsti"; "fsi"])
             in
          if uu____85251 then as_interface m else m  in
        let uu____85272 = desugar_modul_common curmod env m1  in
        match uu____85272 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____85294 = FStar_Syntax_DsEnv.pop ()  in
              (uu____85294, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____85316 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____85316 with
      | (env1,modul,pop_when_done) ->
          let uu____85333 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____85333 with
           | (env2,modul1) ->
               ((let uu____85345 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____85345
                 then
                   let uu____85348 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____85348
                 else ());
                (let uu____85353 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____85353, modul1))))
  
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
        (fun uu____85407  ->
           let uu____85408 = desugar_modul env modul  in
           match uu____85408 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____85450  ->
           let uu____85451 = desugar_decls env decls  in
           match uu____85451 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____85506  ->
             let uu____85507 = desugar_partial_modul modul env a_modul  in
             match uu____85507 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____85606 ->
                  let t =
                    let uu____85616 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____85616  in
                  let uu____85629 =
                    let uu____85630 = FStar_Syntax_Subst.compress t  in
                    uu____85630.FStar_Syntax_Syntax.n  in
                  (match uu____85629 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____85642,uu____85643)
                       -> bs1
                   | uu____85668 -> failwith "Impossible")
               in
            let uu____85678 =
              let uu____85685 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____85685
                FStar_Syntax_Syntax.t_unit
               in
            match uu____85678 with
            | (binders,uu____85687,binders_opening) ->
                let erase_term t =
                  let uu____85695 =
                    let uu____85696 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____85696  in
                  FStar_Syntax_Subst.close binders uu____85695  in
                let erase_tscheme uu____85714 =
                  match uu____85714 with
                  | (us,t) ->
                      let t1 =
                        let uu____85734 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____85734 t  in
                      let uu____85737 =
                        let uu____85738 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____85738  in
                      ([], uu____85737)
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
                    | uu____85761 ->
                        let bs =
                          let uu____85771 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____85771  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____85811 =
                          let uu____85812 =
                            let uu____85815 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____85815  in
                          uu____85812.FStar_Syntax_Syntax.n  in
                        (match uu____85811 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____85817,uu____85818) -> bs1
                         | uu____85843 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____85851 =
                      let uu____85852 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____85852  in
                    FStar_Syntax_Subst.close binders uu____85851  in
                  let uu___4311_85853 = action  in
                  let uu____85854 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____85855 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_85853.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_85853.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____85854;
                    FStar_Syntax_Syntax.action_typ = uu____85855
                  }  in
                let uu___4313_85856 = ed  in
                let uu____85857 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____85858 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____85859 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____85860 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____85861 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____85862 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____85863 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____85864 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____85865 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____85866 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____85867 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____85868 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____85869 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____85870 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____85871 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____85872 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_85856.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_85856.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____85857;
                  FStar_Syntax_Syntax.signature = uu____85858;
                  FStar_Syntax_Syntax.ret_wp = uu____85859;
                  FStar_Syntax_Syntax.bind_wp = uu____85860;
                  FStar_Syntax_Syntax.if_then_else = uu____85861;
                  FStar_Syntax_Syntax.ite_wp = uu____85862;
                  FStar_Syntax_Syntax.stronger = uu____85863;
                  FStar_Syntax_Syntax.close_wp = uu____85864;
                  FStar_Syntax_Syntax.assert_p = uu____85865;
                  FStar_Syntax_Syntax.assume_p = uu____85866;
                  FStar_Syntax_Syntax.null_wp = uu____85867;
                  FStar_Syntax_Syntax.trivial = uu____85868;
                  FStar_Syntax_Syntax.repr = uu____85869;
                  FStar_Syntax_Syntax.return_repr = uu____85870;
                  FStar_Syntax_Syntax.bind_repr = uu____85871;
                  FStar_Syntax_Syntax.actions = uu____85872;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_85856.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_85888 = se  in
                  let uu____85889 =
                    let uu____85890 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____85890  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85889;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_85888.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_85888.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_85888.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_85888.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_85894 = se  in
                  let uu____85895 =
                    let uu____85896 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85896
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85895;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_85894.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_85894.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_85894.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_85894.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____85898 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____85899 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____85899 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____85916 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____85916
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____85918 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____85918)
  